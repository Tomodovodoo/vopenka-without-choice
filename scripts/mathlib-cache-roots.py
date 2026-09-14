"""List the directly imported mathlib modules, without downloading all mathlib."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
sources = [root / 'ZFVP', root / 'vendor/Foundation', *root.glob('Palomar*Bridge')]
modules = set()
for source in sources:
    for path in source.rglob('*.lean'):
        modules.update(re.findall(r'^import\s+(Mathlib(?:\.[\w.]+)?)\s*$',
                                  path.read_text(encoding='utf-8'), re.M))
if not modules:
    raise SystemExit('No mathlib cache roots found.')
print('\n'.join(sorted(modules)))
