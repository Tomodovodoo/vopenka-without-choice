"""Render V2 left and V3 right, colouring changed V3 words red."""
import argparse
from difflib import SequenceMatcher
from pathlib import Path
import re
import unicodedata
import zipfile

import fitz
from PIL import Image, ImageDraw, ImageFont

parser = argparse.ArgumentParser()
parser.add_argument('v2', type=Path)
parser.add_argument('destination', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
args.destination.mkdir(parents=True, exist_ok=True)
before = fitz.open(args.v2)
after = fitz.open(root / 'paper/vopenka_without_choice_V3.pdf')
pages = [6, 11, 13, 14, 17, 19]


def tokens(document):
    result = []
    for page_number, page in enumerate(document):
        words = [w for w in page.get_text('words')
                 if w[1] >= 65 and w[3] <= 790 and w[0] >= 60]
        for word in words:
            text = unicodedata.normalize('NFKC', word[4])
            location = (page_number, fitz.Rect(word[:4]))
            if (result and result[-1][1][-1][0] == page_number
                    and re.search(r'[A-Za-z]+-$', result[-1][0])
                    and re.match(r'[A-Za-z]', text)
                    and word[1] > result[-1][1][-1][1].y0 + 3):
                old, locations = result[-1]
                result[-1] = (old[:-1] + text, locations + [location])
            else:
                result.append((text, [location]))
    return result


old, new = tokens(before), tokens(after)
changed = set()
for operation, _, _, start, end in SequenceMatcher(
        None, [t[0] for t in old], [t[0] for t in new], autojunk=False).get_opcodes():
    if operation in {'insert', 'replace'}:
        changed.update(range(start, end))
for index in changed:
    for page_number, rectangle in new[index][1]:
        # Screen blending turns black glyphs red and leaves white paper white.
        # The original text, fonts and layout remain intact.
        annotation = after[page_number].add_rect_annot(rectangle)
        annotation.set_colors(stroke=None, fill=(1, 0, 0))
        annotation.set_border(width=0)
        annotation.set_opacity(1)
        annotation.set_blendmode('Screen')
        annotation.update()

after.save(args.destination / 'V3-red-changes.pdf', garbage=4, deflate=True)
font = ImageFont.load_default(size=28)
comparison = fitz.open()
for number in pages:
    left_path = args.destination / f'page-{number:02}-V2.png'
    right_path = args.destination / f'page-{number:02}-V3-red.png'
    before[number-1].get_pixmap(matrix=fitz.Matrix(2, 2)).save(left_path)
    after[number-1].get_pixmap(matrix=fitz.Matrix(2, 2)).save(right_path)
    left, right = Image.open(left_path), Image.open(right_path)
    gutter, top = 24, 54
    canvas = Image.new('RGB', (left.width + right.width + gutter,
                              max(left.height, right.height) + top), 'white')
    canvas.paste(left, (0, top))
    canvas.paste(right, (left.width + gutter, top))
    draw = ImageDraw.Draw(canvas)
    draw.text((24, 10), f'V2 · page {number}', font=font, fill='black')
    draw.text((left.width + gutter + 24, 10),
              f'V3 · page {number} · changes in red', font=font, fill='black')
    combined = args.destination / f'page-{number:02}-comparison.png'
    canvas.save(combined)
    pdf_page = comparison.new_page(width=canvas.width / 2, height=canvas.height / 2)
    pdf_page.insert_image(pdf_page.rect, filename=str(combined))
    print(f'Page {number}: {sum(1 for i in changed if new[i][1][0][0] == number-1)} changed tokens')
comparison.save(args.destination / 'V2-V3-side-by-side.pdf', deflate=True)
with zipfile.ZipFile(args.destination / 'V2-V3-review.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for path in sorted(args.destination.iterdir()):
        if path.suffix in {'.png', '.pdf'}:
            archive.write(path, path.name)
print(args.destination)
