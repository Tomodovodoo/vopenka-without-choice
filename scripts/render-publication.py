"""Render the publication PDFs and key paper pages for review."""
import argparse
from pathlib import Path

import fitz
from PIL import Image, ImageDraw

parser = argparse.ArgumentParser()
parser.add_argument('destination', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
args.destination.mkdir(parents=True, exist_ok=True)

for name, source in [('paper', 'vopenka_without_choice_V3.pdf'),
                     ('supplement', 'supplement.pdf')]:
    doc = fitz.open(root / 'paper' / source)
    for number, page in enumerate(doc, 1):
        page.get_pixmap(matrix=fitz.Matrix(1.6, 1.6)).save(
            args.destination / f'{name}-{number:02}.png')
    for start in range(0, len(doc), 4):
        sheet = Image.new('RGB', (1400, 2000), 'white')
        draw = ImageDraw.Draw(sheet)
        for offset in range(min(4, len(doc) - start)):
            number = start + offset + 1
            page = Image.open(args.destination / f'{name}-{number:02}.png')
            page.thumbnail((670, 950))
            x, y = (offset % 2) * 700 + 15, (offset // 2) * 1000 + 35
            sheet.paste(page, (x, y))
            draw.text((x, y - 22), f'{name}, page {number}', fill='black')
        sheet.save(args.destination / f'{name}-contact-{start // 4 + 1}.png')
    if name == 'paper':
        for number in [6, 7, 11, 13, 14, 17, 19]:
            page = doc[number - 1]
            for phrase in ['Supplement', 'completed', 'finite dictionary',
                           'sufficient', 'same extension', 'membership language',
                           'marked', 'relativization']:
                for rectangle in page.search_for(phrase):
                    annotation = page.add_highlight_annot(rectangle)
                    annotation.set_colors(stroke=(0.3, 0.65, 1))
                    annotation.update()
            page.get_pixmap(matrix=fitz.Matrix(1.6, 1.6)).save(
                args.destination / f'changes-{number:02}.png')
print(args.destination)
