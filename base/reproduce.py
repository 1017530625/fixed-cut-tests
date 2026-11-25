"""Reconstruct and verify this source supplement in a separate directory."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


BUNDLE = Path(__file__).resolve().parent
P118 = 'ProofBench/PROBLEMS/P118/P118.lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data):
    return sha256(data).hexdigest()


def hash_file(path):
    return digest(path.read_bytes())


def save_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf8')


def verify_payload():
    checks = {}
    for line in (BUNDLE/'SHA256SUMS').read_text(encoding='utf8').splitlines():
        expected, name = line.split('  ', 1)
        if name in checks or not re.fullmatch('[a-f0-9]{64}', expected):
            raise ValueError('invalid checksum entry for '+name)
        checks[name] = expected
    for name, expected in checks.items():
        if hash_file(BUNDLE/name) != expected:
            raise ValueError('invalid payload: '+name)
    return checks


def capture(args, cwd):
    return subprocess.check_output(args, cwd=cwd, stderr=subprocess.STDOUT)


def run(args, cwd, logs, label):
    path = logs/(label+'.log')
    header = {'start_utc':datetime.now(timezone.utc).isoformat(), 'argv':args, 'cwd':str(cwd)}
    print(label, flush=True)
    start = time.monotonic()
    with path.open('wb') as out:
        out.write((json.dumps(header, ensure_ascii=False)+'\n').encode())
        out.flush()
        result = subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        out.write(('\n'+json.dumps({'exit':result.returncode,'seconds':round(time.monotonic()-start,3)})
                   +'\n').encode())
    if result.returncode:
        raise RuntimeError(f'{label} exited with {result.returncode}. See {path}')
    return path


def git_object(repo, ref, name):
    return capture(['git','show',ref+':'+name], repo)


def check_packages(packages, deps):
    observed = {}
    for item in deps:
        if item.get('type') != 'git':
            raise ValueError('expected locked git dependency: '+item['name'])
        dep = packages/item['name']
        actual = capture(['git','rev-parse','HEAD'], dep).decode().strip()
        if actual != item['rev']:
            raise ValueError(f'{dep}: {actual} does not match {item["rev"]}')
        dirty = capture(['git','status','--porcelain','--untracked-files=no'], dep).decode().strip()
        if dirty:
            raise ValueError('dependency contains tracked modifications: '+str(dep))
        observed[item['name']] = actual
    return observed


def connect_packages(project, source):
    target = project/'.lake/packages'
    target.parent.mkdir(exist_ok=True)
    if target.exists():
        if not target.samefile(source):
            raise ValueError('existing workspace uses a different dependency directory')
        return
    if os.name == 'nt':
        env = dict(os.environ, ARTIFACT_CACHE_LINK=str(target), ARTIFACT_CACHE_TARGET=str(source))
        subprocess.run(['powershell.exe','-NoProfile','-Command',
                        'New-Item -ItemType Junction -Path $env:ARTIFACT_CACHE_LINK '
                        '-Target $env:ARTIFACT_CACHE_TARGET -ErrorAction Stop | Out-Null'],
                       env=env, check=True)
    else:
        target.symlink_to(source, target_is_directory=True)


def p118_bytes(upstream, spec):
    if digest(upstream) != spec['upstream_git_lf_sha256']:
        raise ValueError('P118 upstream content differs from the frozen source')
    lines = upstream.splitlines(keepends=True)
    start = spec['insert_before_line']-1
    hole = spec['replace_line']-1
    if len(lines) != hole+1 or lines[hole].strip() != b'sorry':
        raise ValueError('expected proof hole absent in the pinned upstream source')
    prefix = b''.join(lines[:start])
    signature = b''.join(lines[start:hole])
    if digest(prefix) != spec['upstream_prefix_sha256'] or digest(signature) != spec['theorem_header_sha256']:
        raise ValueError('pinned prefix or theorem signature differs')
    raw = (prefix + (BUNDLE/spec['helpers']).read_bytes() + signature
           + (BUNDLE/spec['body']).read_bytes())
    if spec['output_eol']=='CRLF':
        raw = raw.replace(b'\n',b'\r\n')
    return raw


def initialize(work, upstream, ref, stamp, logs):
    marker = work/'bundle-id'
    project = work/'project'
    if not marker.exists():
        marker.write_text(stamp+'\n', encoding='ascii')
    if marker.read_text(encoding='ascii').strip() != stamp:
        raise ValueError('existing work directory belongs to a different artifact version')
    if not (project/'.git').exists():
        run(['git','clone','--no-checkout','--no-hardlinks','--config','core.autocrlf=false',
             str(upstream),str(project)], work, logs, 'clone')
        run(['git','-c','core.autocrlf=false','checkout','--detach',ref], project, logs, 'checkout')
    if capture(['git','rev-parse','HEAD'], project).decode().strip() != ref:
        raise ValueError('scratch checkout has an unexpected HEAD')
    return project


def materialize(project, manifest):
    ref = manifest['upstream']['commit']
    for name, expected in manifest['pinned_inputs'].items():
        if digest(git_object(project, ref, name)) != expected or hash_file(project/name) != expected:
            raise ValueError('pinned project configuration changed: '+name)
    rebuilt = {}
    for name, expected in manifest['materialized_sha256'].items():
        if name == P118:
            data = p118_bytes(git_object(project,ref,P118), manifest['proof_fragments'])
        else:
            data = (BUNDLE/'overlay'/name).read_bytes()
        if digest(data) != expected:
            raise ValueError('source materialization mismatch: '+name)
        dest = project/name
        dest.parent.mkdir(exist_ok=True, parents=True)
        if dest.exists() and dest.read_bytes() != data:
            replaceable = name == P118 and dest.read_bytes() == git_object(project,ref,P118)
            if not replaceable:
                raise ValueError('existing source was changed; use a fresh work directory: '+name)
        if not dest.exists() or dest.read_bytes() != data:
            dest.write_bytes(data)
        rebuilt[name] = hash_file(dest)
        if rebuilt[name] != expected:
            raise ValueError('disk hash mismatch: '+name)
    return rebuilt


def checked_axioms(report, names):
    result = {}
    for name in names:
        matches = re.findall(r"^'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",report,re.M)
        empty = report.count("'"+name+"' does not depend on any axioms")
        if len(matches)+empty != 1:
            raise ValueError('missing or duplicate axiom record: '+name)
        axioms = sorted(a.strip() for a in matches[0].split(',') if a.strip()) if matches else []
        if set(axioms)-ALLOWED:
            raise ValueError(name+' has unexpected axioms: '+str(axioms))
        result[name] = axioms
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, required=True, help='local LPBench git clone')
    parser.add_argument('--work', type=Path, required=True, help='empty directory or this runner’s earlier scratch')
    parser.add_argument('--packages', type=Path, help='optional pinned, prebuilt .lake/packages directory')
    parser.add_argument('--kernel-replay', action='store_true', help='also run leanchecker on the designated modules')
    args = parser.parse_args()
    checks = verify_payload()
    manifest = json.loads((BUNDLE/'manifest.json').read_text(encoding='utf8'))
    upstream = args.upstream.resolve(strict=True)
    work = args.work.resolve()
    if work.is_relative_to(BUNDLE) or work.is_relative_to(upstream):
        raise ValueError('choose a work directory outside the bundle and upstream checkout')
    if work.exists() and any(work.iterdir()) and not (work/'bundle-id').is_file():
        raise ValueError('choose an empty work directory; existing files are preserved')
    work.mkdir(exist_ok=True, parents=True)
    logs = work/'logs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    logs.mkdir(exist_ok=False, parents=True)
    ref = manifest['upstream']['commit']
    project = initialize(work,upstream,ref,hash_file(BUNDLE/'SHA256SUMS'),logs)
    sources = materialize(project, manifest)
    save_json(logs/'materialized.json',sources)
    locked = json.loads((project/'lake-manifest.json').read_text(encoding='utf8'))['packages']
    if args.packages:
        supplied = args.packages.resolve(strict=True)
        check_packages(supplied,locked)
        connect_packages(project,supplied)
    else:
        run(['lake','exe','cache','get'],project,logs,'dependency-cache')
    dependencies = check_packages(project/'.lake/packages',locked)
    save_json(logs/'dependency-revisions.json',dependencies)
    version = capture(['lean','--version'],project).decode().strip()
    if '4.34.1' not in version or '5045d005' not in version:
        raise ValueError('unexpected Lean version: '+version)
    run(['lake','build',*manifest['build_modules']],project,logs,'build')
    for name, expected in manifest['pinned_inputs'].items():
        if hash_file(project/name)!=expected:
            raise ValueError('dependency resolution changed the lock: '+name)
    audit = project/'P118StudyAxioms.lean'
    declarations = manifest['audit_declarations']
    audit.write_text('\n'.join('import '+m for m in manifest['build_modules'])+'\n'
                     +'\n'.join('#print axioms '+name for name in declarations)+'\n',encoding='utf8')
    printed = run(['lake','env','lean',audit.name],project,logs,'axioms')
    axioms = checked_axioms(printed.read_text(encoding='utf8'),declarations)
    for test in ('PaperContracts','NontrivialNestedCycle'):
        path = run(['lake','env','lean',str(BUNDLE/'checks'/(test+'.lean'))],project,logs,test)
        checked_axioms(path.read_text(encoding='utf8'),manifest['supplemental_axioms'][test])
    countlog = run([sys.executable,str(BUNDLE/'checks'/'enumerate_cuts.py')],work,logs,'enumerate-cuts')
    numbers = json.loads('\n'.join(countlog.read_text(encoding='utf8').splitlines()[1:-2]))
    if (numbers['canonical_proper_cuts'],numbers['four_cut_families_examined'],
        numbers['sufficient_four_cut_families'],numbers['sufficient_adjacent_four_cut_families'],
        [r['two_cut_families'] for r in numbers['rings']]) != (127,10334625,1116,9,[144]*4):
        raise ValueError('independent enumeration changed')
    run([sys.executable,str(BUNDLE/'checks'/'cycle24.py')],work,logs,'cycle24')
    if args.kernel_replay:
        run(['lake','env','leanchecker','-v',*manifest['replay_modules']],project,logs,'leanchecker')
    result = {'status':'passed','upstream':ref,'lean':version,'payload_files_checked':len(checks),
              'built':manifest['build_modules'],'materialized_sha256':sources,'axioms':axioms,
              'supplemental_axioms':manifest['supplemental_axioms'],
              'python_checks':{'unlabelled_complements_labelled_vertices':1116,'specified_ring':[144]*4},
              'leanchecker_modules':manifest['replay_modules'] if args.kernel_replay else [],
              'dependency_source':'shared pinned prebuilt packages' if args.packages else 'Lake downloaded pinned dependencies',
              'dependency_revisions':dependencies}
    save_json(logs/'verified.json',result)
    print(f'PASSED: {len(sources)} reconstructed Lean sources, {len(axioms)} main declarations.')
    print(logs/'verified.json')


if __name__=='__main__':
    main()
