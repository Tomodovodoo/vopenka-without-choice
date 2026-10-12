"""Create the single-document arXiv source ZIP and a local review bundle."""
from pathlib import Path
import hashlib
import json
import shutil
import zipfile

root = Path(__file__).resolve().parent.parent
out = root / 'output/publication'
out.mkdir(parents=True, exist_ok=True)
main = root / 'paper/vopenka_without_choice_V3.tex'
paper_pdf = root / 'paper/vopenka_without_choice_V3.pdf'
supplement = root / 'paper/supplement.pdf'
for path in [main, paper_pdf, supplement]:
    if not path.is_file():
        raise SystemExit(f'Missing publication artifact: {path}')
with zipfile.ZipFile(out / 'arxiv-v3-source.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    archive.write(main, 'main.tex')
    archive.write(supplement, 'anc/supplement.pdf')
for path in [paper_pdf, supplement]:
    shutil.copyfile(path, out / path.name)
shutil.copyfile(root / 'docs/submission.md', out / 'submission.md')
manifest = {p.name: {'bytes': p.stat().st_size,
    'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
    for p in sorted(out.iterdir()) if p.is_file() and p.name != 'manifest.json'}
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(out / 'arxiv-v3-source.zip')
