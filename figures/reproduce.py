"""Recreate the original vector figures and, optionally, the journal PDFs."""

import argparse
from dataclasses import dataclass
from hashlib import sha256
from io import BytesIO
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from pypdf import PdfReader, PdfWriter
from pypdf.generic import ArrayObject, NameObject, NumberObject
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas


ROOT = Path(__file__).resolve().parent
MATCHING = Path("evidence/referee/cover-aware-count.json")


@dataclass(frozen=True)
class Figure:
    script: str
    vector: str
    journal: str
    size_pt: tuple[int, int]
    vector_sha256: str
    drawing_sha256: str
    journal_sha256: str


FIGURES = (
    Figure(
        "plot_connected_witness.py", "connected-witness.pdf", "Fig1.pdf", (410, 117),
        "8cb7ffe5a3bc2d80a51a406ca459098fb7e1113245b2fa5a1edf57267f3bbdd6",
        "1b12635a45154356ab1ef5e1e91faff7d4fb5b7d994d62d6585762061c93a72a",
        "27d7812dd96e92cd3a72648bc5a90329f0bca9a444dbe3c195b485a7fcac1d5c",
    ),
    Figure(
        "plot_cycle_triples.py", "cycle24-triples.pdf", "Fig2.pdf", (405, 154),
        "7e0a608733d119aa381f2fc9646798505144fc7bb64f39b8f6a4fdbf46c3dd12",
        "72da443dc4f269cacee101f51c59dd5eaf1b27ca0e1403852ec4ac77e69ffbb1",
        "4c2497c4b69646ca54012e203d5b861940c4ae11f2a5bf4265fc755a31544ccb",
    ),
)


def check_hash(data, expected, label):
    actual = sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"{label} SHA-256 mismatch. Expected {expected}, found {actual}.")


def verify_pdf(path, figure, expected):
    data = path.read_bytes()
    check_hash(data, expected, path.name)
    reader = PdfReader(BytesIO(data))
    if len(reader.pages) != 1 or tuple(reader.pages[0].mediabox) != (0, 0, *figure.size_pt):
        raise ValueError(f"Unexpected page size or page count in {path.name}")
    check_hash(reader.pages[0].get_contents().get_data(), figure.drawing_sha256, path.name + " drawing")
    print(f"{path.name}  {len(data):6d} bytes  {expected}", flush=True)


def journal_fonts(regular_path, bold_path):
    inputs = (
        ("Helvetica", regular_path, "edfbd22a3d088fc2f5d7c79b8c9c732df6dc878a60f0a80be0f92a3c7a634404"),
        ("Helvetica-Bold", bold_path, "4d59199834e7439c67ea4949407639961060b21b173833f566eb60ac6fd8f5af"),
    )
    donor = BytesIO()
    canvas = Canvas(donor, invariant=True)
    postscript_names = {}
    for base, path, expected in inputs:
        data = path.read_bytes()
        check_hash(data, expected, str(path))
        font = TTFont("Figure-" + base, BytesIO(data), asciiReadable=True)
        pdfmetrics.registerFont(font)
        postscript_names[font.face.name.decode("ascii")] = base
        canvas.setFont(font.fontName, 10)
        canvas.drawString(10, 20, "0123456789Qrst ()ab")
    canvas.showPage()
    canvas.save()
    resources = PdfReader(donor).pages[0]["/Resources"]["/Font"]
    subsets = {}
    for ref in resources.values():
        font = ref.get_object()
        if font["/Subtype"] == "/TrueType":
            name = font["/BaseFont"].split("+")[-1]
            subsets[postscript_names[name]] = ref
    return subsets


def embed_fonts(source, destination, subsets):
    writer = PdfWriter(clone_from=source)
    resources = writer.pages[0]["/Resources"]["/Font"]
    for key, ref in list(resources.items()):
        base = ref.get_object()["/BaseFont"][1:]
        resources[NameObject(key)] = subsets[base].clone(writer)
        embedded = resources[key]
        # Preserve the original Base 14 character advances, in thousandths of an em.
        embedded[NameObject("/Widths")] = ArrayObject([
            NumberObject(round(pdfmetrics.stringWidth(chr(code), base, 1000)))
            if 32 <= code <= 126 else width for code, width in enumerate(embedded["/Widths"])
        ])
    with destination.open("wb") as output:
        writer.write(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path, help="new directory for verified PDFs")
    parser.add_argument("--regular-font", type=Path, help="regular journal TrueType font")
    parser.add_argument("--bold-font", type=Path, help="bold journal TrueType font")
    args = parser.parse_args()
    if bool(args.regular_font) != bool(args.bold_font):
        parser.error("supply both --regular-font and --bold-font to reproduce the journal files")
    out = args.out.resolve()
    if out.exists():
        parser.error(f"choose a new output directory. {out} already exists")
    subsets = journal_fonts(args.regular_font, args.bold_font) if args.regular_font else None
    out.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=out.parent) as temporary:
        stage = Path(temporary)
        scripts = stage / "scripts"
        scripts.mkdir()
        (stage / MATCHING).parent.mkdir(parents=True)
        shutil.copyfile(ROOT / MATCHING, stage / MATCHING)
        pdfs = stage / "manuscripts/figures"
        pdfs.mkdir(parents=True)
        for figure in FIGURES:
            plot = scripts / figure.script
            shutil.copyfile(ROOT / "scripts" / figure.script, plot)
            subprocess.run([sys.executable, "-B", str(plot)], cwd=stage, check=True)
            source = pdfs / figure.vector
            verify_pdf(source, figure, figure.vector_sha256)
            if subsets:
                journal = pdfs / figure.journal
                embed_fonts(source, journal, subsets)
                verify_pdf(journal, figure, figure.journal_sha256)
        pdfs.rename(out)


if __name__ == "__main__":
    main()
