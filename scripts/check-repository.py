"""Check repository structure; --submission also enforces the known intake gates.

This is a local preflight, not Palomar's verifier or an editorial review.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser()
parser.add_argument('--submission', action='store_true')
parser.add_argument('--report', type=Path)
args = parser.parse_args()
errors, blockers = [], []
config = json.loads((ROOT / 'comparator.json').read_text())
required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
if not required <= config.keys():
    errors.append('Comparator configuration lacks required fields.')
if not config.get('theorem_names') or not set(config['permitted_axioms']) <= {'propext', 'Quot.sound', 'Classical.choice'}:
    errors.append('Invalid compared declarations or permitted axioms.')
if config.get('enable_nanoda') is not True:
    errors.append('NanoDa must be enabled.')
if config['challenge_module'] == config['solution_module']:
    errors.append('Challenge and Solution must be separate modules.')

def module_path(name):
    path = Path(*name.split('.')).with_suffix('.lean')
    for base in [ROOT, ROOT / 'vendor/Foundation']:
        if (base / path).is_file():
            return base / path
    return None

def imports(path):
    # Drop nested Lean comments before reading imports and proof holes.
    return re.findall(r'^import\s+(\S+)', strip_comments(path.read_text(encoding='utf-8')), re.M)

def strip_comments(text):
    output, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-': depth += 1; i += 2
        elif depth and text[i:i+2] == '-/': depth -= 1; i += 2
        elif depth: output.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            output.append(' '); i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else: output.append(text[i]); i += 1
    return ''.join(output)

challenge = module_path(config['challenge_module'])
solution = module_path(config['solution_module'])
for path in [challenge, solution]:
    if path is None: errors.append('A compared module is missing.')
if challenge:
    if challenge.stat().st_size > 102400 or len(challenge.read_text(encoding='utf-8').splitlines()) > 1000:
        blockers.append('Challenge exceeds Palomar size limit.')
    pending, seen = [challenge], set()
    while pending:
        path = pending.pop()
        if path in seen: continue
        seen.add(path)
        for name in imports(path):
            local = module_path(name)
            if local: pending.append(local)
            elif name.startswith(('ZFVP.', 'Foundation.')): errors.append(f'Missing local import {name}')
    disallowed = sorted(str(p.relative_to(ROOT)).replace('\\', '/') for p in seen if p != challenge)
    if disallowed:
        blockers.append(f'Challenge imports {len(disallowed)} project/Foundation source files; Palomar forbids this transitive closure.')
else:
    disallowed = []

files = subprocess.check_output(['git', 'ls-files'], cwd=ROOT, text=True).splitlines()
proof_holes = []
for name in files:
    path = ROOT / name
    if path.suffix == '.lean' and path != challenge:
        if re.search(r'\b(sorry|admit|sorryAx)\b', strip_comments(path.read_text(encoding='utf-8'))):
            proof_holes.append(name)
if proof_holes: errors.append(f'Proof holes outside Challenge: {proof_holes}')
for directory in ['docs', 'repairs', 'paper']:
    for path in (ROOT / directory).rglob('*.md'):
        for target in re.findall(r'\]\(([^)]+)\)', path.read_text(encoding='utf-8')):
            target = target.split('#')[0]
            if target and '://' not in target and not (path.parent / target).exists():
                errors.append(f'Broken link in {path.relative_to(ROOT)}: {target}')
if not (ROOT / 'LICENSE').is_file(): blockers.append('Root LICENSE is not yet selected.')
metadata = ROOT / 'formalization.yaml'
if not metadata.is_file(): errors.append('formalization.yaml is missing.')
else:
    # This repository writes JSON syntax, which is also valid YAML. Keep the
    # preflight dependency-free; CI separately checks the upstream YAML schema.
    data = json.loads(metadata.read_text(encoding='utf-8'))
    if data.get('status', {}).get('sorry_count') != len(proof_holes):
        errors.append('Metadata proof-hole count differs from the source scan.')
    if data.get('project', {}).get('license', '').startswith('LicenseRef-'):
        blockers.append('Metadata does not yet name a Palomar-accepted standard license.')
if args.submission:
    try:
        visibility = subprocess.check_output(
            ['gh', 'repo', 'view', '--json', 'visibility', '--jq', '.visibility'],
            cwd=ROOT, text=True).strip()
        if visibility != 'PUBLIC': blockers.append('The GitHub repository is not public.')
    except (OSError, subprocess.CalledProcessError):
        blockers.append('Could not verify public GitHub visibility.')
report = {'repository_errors': errors, 'submission_blockers': blockers,
          'challenge_project_imports': disallowed, 'proof_holes': proof_holes,
          'comparator_config_sha256': hashlib.sha256((ROOT / 'comparator.json').read_bytes()).hexdigest()}
if args.report:
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k != 'challenge_project_imports'}, indent=2))
sys.exit(bool(errors or args.submission and blockers))
