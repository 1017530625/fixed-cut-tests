"""Draw the six-cycle and the three-leaf separation witness for the manuscript."""

import json
from math import cos, pi, sin
from pathlib import Path

from reportlab.lib.colors import HexColor, white
from reportlab.pdfgen.canvas import Canvas


OUT = Path(__file__).resolve().parents[1]
INK = HexColor("#202d37")
ACCENT = HexColor("#15574e")
MUTED = HexColor("#586771")


def vertex(canvas, x, y, label, radius=8):
    canvas.setFillColor(white)
    canvas.setStrokeColor(INK)
    canvas.setLineWidth(0.8)
    canvas.circle(x, y, radius, stroke=1, fill=1)
    canvas.setFillColor(INK)
    canvas.setFont("Helvetica", 9)
    canvas.drawCentredString(x, y - 3, label)


def main():
    data = json.loads((OUT / "evidence/referee/cover-aware-count.json").read_text())
    ring = next(r for r in data["rings"] if sorted(r["vertices"]) == list(range(1, 7)))
    matching = {tuple(edge) for edge in ring["matchings"][0]}
    cycle = [1, 3, 2, 6, 4, 5]
    edges = list(zip(cycle, cycle[1:] + cycle[:1]))
    assert all((v ^ w).bit_count() == 1 for v, w in edges)
    assert matching == {(1, 3), (2, 6), (4, 5)}
    target = OUT / "manuscripts/figures/connected-witness.pdf"
    canvas = Canvas(str(target), pagesize=(410, 117), invariant=1)
    canvas.setTitle("An alternating matching and its connected realization")
    coordinates = {
        v: (98 + 49 * cos(pi * i / 3), 55 + 41 * sin(pi * i / 3))
        for i, v in enumerate(cycle)
    }
    for u, v in edges:
        chosen = tuple(sorted((u, v))) in matching
        canvas.setStrokeColor(ACCENT if chosen else MUTED)
        canvas.setLineWidth(3.6 if chosen else 0.8)
        canvas.line(*coordinates[u], *coordinates[v])
    for v in cycle:
        vertex(canvas, *coordinates[v], str(v))
    hub = (297, 56)
    leaves = [(251, 18), (297, 95), (344, 18)]
    canvas.setStrokeColor(INK)
    canvas.setLineWidth(1)
    for p in leaves:
        canvas.line(*hub, *p)
    for (u, v), p in zip(sorted(matching), leaves, strict=True):
        vertex(canvas, *p, f"{u}{v}", radius=10)
    vertex(canvas, *hub, "Q", radius=10)
    canvas.setFont("Helvetica-Bold", 9)
    canvas.drawString(6, 106, "(a)")
    canvas.drawString(213, 106, "(b)")
    canvas.save()


if __name__ == "__main__":
    main()
