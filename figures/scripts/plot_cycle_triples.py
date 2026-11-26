"""Draw the endpoint pairs for the two oriented separation triples on C24."""
from math import cos, pi, sin
from pathlib import Path
from reportlab.lib.colors import HexColor, white
from reportlab.pdfgen.canvas import Canvas


TRIPLES = (
    ((20, 8), (12, 0), (4, 16)),
    ((0, 12), (8, 16), (4, 20)),
)
TARGET = Path(__file__).resolve().parents[1] / 'manuscripts/figures/cycle24-triples.pdf'


def panel(page, x_center, pairs, panel_name):
    radius = 52
    ink = HexColor('#263039')
    tones = [HexColor('#265b66'), HexColor('#845333'), HexColor('#45415f')]
    dashes = [(4, 2.6), (1.7, 2), (6, 2, 1, 2)]

    def point(v, distance):
        angle = pi / 2 - v * pi / 12
        return x_center + distance * cos(angle), 78 + distance * sin(angle)

    names = {}
    for i, (first, last) in enumerate(pairs):
        name = 'rst'[i]
        names[first] = names[last] = name
        page.setDash(dashes[i])
        page.setStrokeColor(tones[i])
        page.setLineWidth(1.0)
        page.line(*point(first, radius), *point(last, radius))
    page.setDash([])
    page.setStrokeColor(ink)
    page.setFillColor(ink)
    page.setLineWidth(1.15)
    for v in range(24):
        page.line(*point(v, radius), *point((v + 1) % 24, radius))
    for v in range(24):
        x, y = point(v, radius)
        if v not in names:
            page.setFillColor(ink)
            page.circle(x, y, 1.65, stroke=0, fill=1)
            continue
        page.setFillColor(white)
        page.circle(x, y, 3.1, stroke=1, fill=1)
        page.setFillColor(ink)
        page.setFont('Helvetica', 9.3)
        label = f'{v} ({names[v]})'
        if v in (0, 12):
            label_x, label_y = point(v, radius + 11.4)
            page.drawCentredString(label_x, label_y - 3, label)
        else:
            label_x, label_y = point(v, radius + 7.8)
            align = page.drawString if x > x_center else page.drawRightString
            align(label_x, label_y - 3, label)
    page.setFont('Helvetica-Bold', 10)
    page.drawString(x_center - 83, 140, panel_name)


def main():
    page = Canvas(str(TARGET), pagesize=(405,154), invariant=True)
    page.setTitle('Two separation triples on the same 24-cycle')
    panel(page, 102, TRIPLES[0], '(a)')
    panel(page, 303, TRIPLES[1], '(b)')
    page.showPage()
    page.save()


if __name__ == '__main__':
    main()
