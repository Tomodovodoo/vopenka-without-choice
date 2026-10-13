"""Apply the publication edits to the archived arXiv v2 source."""
from pathlib import Path
import difflib
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
baseline = root / 'paper/arxiv-v2.tex'
source = baseline.read_text(encoding='utf-8')
text = source
edits = json.loads((root / 'verification/v14-edit-map.json').read_text())['edits']
skip = {'References', 'Lemma 5.12 label rigidity', 'Lemma 5.12 parameters',
        'Lemma 5.12 properness', 'Theorem 5.13 Bagaria application',
        'Corollary 3.4 certificate rank'}
applied = []
for edit in edits:
    if edit['locus'] in skip:
        continue
    assert text.count(edit['old']) == 1, edit['locus']
    text = text.replace(edit['old'], edit['new'])
    applied.append({'locus': edit['locus'], 'reason': edit['reason']})

def replace(old, new, locus):
    global text
    assert text.count(old) == 1, locus
    text = text.replace(old, new)
    applied.append({'locus': locus})

# The supplied leastness certificate is accommodated explicitly by the rank.
replace('That set and the satisfaction relation of $V_\\theta$ lie in $V_{\\theta+\\omega}$.',
        'The satisfaction relation of $V_\\theta$ lies in $V_{\\theta+\\omega}$.',
        'Certificate containment')
start = text.index('Choose $\\rho>\\omega$', text.index('\\label{cor:Pi-preservation}'))
end = text.index('\\end{proof}', start)
part = text[start:end]
part = part.replace('In the set-sized language with membership, finitely many distinguished constants, and constants for $V_\\rho$, let',
    'Put $h_\\alpha=\\max\\{\\theta_\\alpha,\\rank(d_\\alpha)\\}+\\omega$.  In the set-sized language with membership, finitely many distinguished constants, and constants for $V_\\rho$, let')
part = part.replace('V_{\\theta_\\alpha+\\omega}', 'V_{h_\\alpha}')
part = part.replace('and the other clauses are bounded or $\\Delta_1$.',
    'and the other clauses, including the definition of $h_\\alpha$, are bounded or $\\Delta_1$.')
text = text[:start] + part + text[end:]

start = text.index('\\begin{lemma}\\label{lem:finite-language-reduction}')
end = text.index('\\end{lemma}', start) + len('\\end{lemma}')
text = text[:start] + r'''\begin{lemma}\label{lem:finite-language-reduction}
For every finite set $F_0$ of instances of the arbitrary-language Vop\v{e}nka scheme, there is an effectively determined $N\geq1$ such that
\[
\ZF+\text{``the $E_N$-cardinals are unbounded''}\vdash F_0.
\]
\end{lemma}''' + text[end:]
start = text.index('\\begin{proof}', start)
end = text.index('\\end{proof}', start) + len('\\end{proof}')
text = text[:start] + r'''\begin{proof}
For each class formula, the proof of Lemma~\ref{lem:OH-VP} uses a sufficient level computed from syntactic bounds for that formula and the fixed definitions of structure codes, syntax and satisfaction.  Include both polarities in the bound.  These bounds are independent of the language and parameter values.  Take a common bound for the finitely many instances in $F_0$; see \cite[Section~2]{Supplement}.
\end{proof}''' + text[end:]
start = text.index('Now assume that $\\mathfrak M\\models\\neg\\AC$.')
end = text.index('\n\nEvery finite subset', start)
text = text[:start] + r'''Assume that $\mathfrak M\models\neg\AC$.  Choose $N\geq1$ for the instances of $\VP$ in $F$ by Lemma~\ref{lem:finite-language-reduction}, choose $t_N$ as in Theorem~\ref{thm:finite-restoration}, and choose in $\mathfrak M$ a sufficiently large $E_{t_N}$-cardinal $\Lambda$.  Let $H\subseteq(\mathbb Q_\Lambda)^{\mathfrak M}$ be $\mathfrak M$-generic and put $W=(\mathfrak M[H])_\Lambda$.  For a possibly ill-founded $\mathfrak M$, use its internal names modulo generic forced equality, with membership given by generic forced membership.  The truth lemma holds for each standard formula.  Theorem~\ref{thm:finite-restoration} gives $W\models\ZFC$ with unbounded $E_N$-cardinals, so Lemma~\ref{lem:finite-language-reduction} gives $W\models F$.''' + text[end:]

old = r"Over $\ZFC$, $\VP(\Pi_m)$ is equivalent to the unboundedness of the cardinals satisfying $K_m$ \cite[Theorem~4.3(2), Corollary~4.7, Theorem~4.11, and the paragraph following Theorem~4.12]{BagariaCn}; arbitrary set-sized languages reduce to the usual coding under Choice \cite[Lemma~23]{BrookeTaylor}."
new = r"Over $\ZFC$, $\VP(\Pi_m)$ implies unboundedly many $K_m$-cardinals \cite[Theorem~4.3(2), Corollary~4.7, and the paragraph following Theorem~4.12]{BagariaCn}.  Conversely, for a $\Pi_m$ class choose such a cardinal $\kappa$ above its language and parameters and a class member outside $H_\kappa$.  Regarding the definition as $\Sigma_{m+1}$, \cite[Theorems~4.5 and~4.11]{BagariaCn} gives a distinct reflected member in $H_\kappa$.  Thus the equivalence holds with our language convention."
replace(old, new, 'Proposition 9.1 language convention')

start = text.index('Use the completed presentation and prefix-agreement result of', text.index(r'\label{lem:Woodin-endpoint-forcing}'))
end = text.index('\n\n', start)
text = text[:start] + r"Use the completed presentation of \cite[Section~3.1]{Supplement}.  Every completed prefix through $\eta<\gamma$, with its order and projection maps, belongs to $V_\gamma$.  The fixed defining dictionary computes these prefixes at the supercompact endpoint." + text[end:]

text = text.replace('Instead of choosing one name at each rank, the proof uses', 'The proof uses')
text = text.replace('We now apply Woodin\'s forcing', 'We apply Woodin\'s forcing')
text = text.replace('the repaired existence input in', 'the membership-language existence theorem in')
text = text.replace('Woodin supplement, low-name truth', 'Section~3.3')
text = text.replace('Woodin supplement', 'Section~3')
text = text.replace('Karagila--Schilhan supplement', 'Proposition~4.2')
text = text.replace('Enayat supplement', 'Theorem~5.1')
text = text.replace('{RepairNotes}', '{Supplement}')
text = text.replace('recorded in \\cite[Section~3]{Supplement}', 'proved in \\cite[Section~3]{Supplement}')
text = text.replace('\\begin{theorem}[Woodin, restricted formulation]', '\\begin{theorem}[Woodin]')
text = text.replace('\\cite[Corollary~4.5]{Usuba}.', '\\cite[Corollary~4.5]{Usuba}; see also \\cite[Section~6]{Supplement} for the class-forcing construction.')
intro = 'All forcing notions have a largest condition'
replace(intro,
    'The supplementary material \\cite{Supplement} contains the supporting construction arguments and a correspondence with the Lean formalization.\n\n' + intro,
    'Supplement citation')
replace('\\end{thebibliography}', r'''\bibitem{Supplement}
T.~de Groot and W.~A.~Wo{\l}oszyn,
\emph{Supplementary proofs for Vop\v{e}nka's principle without Choice},
supplementary material accompanying this article, 2026.

\end{thebibliography}''', 'Supplement bibliography')
# Keep the mathematical text unmarked and remove the v2 markup machinery.
text = re.sub(r'% Blue passages.*\n% Change.*\n', '', text)
text = text.replace('\\newif\\ifrevisionblue\n\\revisionbluefalse\n\\DeclareRobustCommand{\\revision}[1]{{\\ifrevisionblue\\color{blue}\\fi#1}}',
                    '\\DeclareRobustCommand{\\revision}[1]{#1}')
out = root / 'paper/vopenka_without_choice_V3.tex'
out.write_text(text, encoding='utf-8')
(root / 'paper/v2-to-v3.diff').write_text(''.join(difflib.unified_diff(
    source.splitlines(True), text.splitlines(True), fromfile='arxiv-v2.tex',
    tofile=out.name)), encoding='utf-8')
(root / 'verification/v3-edit-map.json').write_text(json.dumps({
    'base': 'arxiv:2609.06856v2', 'base_sha256': hashlib.sha256(baseline.read_bytes()).hexdigest(),
    'output': out.name, 'edits': applied}, indent=2)+'\n', encoding='utf-8')
print(out)
