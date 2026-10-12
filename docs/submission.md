# Paper and formalization submission

The paper and supplement are archived together on arXiv. The repository holds
their editable sources and the Lean development. Palomar registers the selected
formal statements, proofs and review at an immutable repository commit.

## Published material

The article is arXiv:2609.06856. Upload the source archive produced by
`python scripts/package-publication.py` using **Replace** on that article.
The archive has one compilable document:

```text
main.tex
anc/
  supplement.pdf
```

`main.tex` contains its bibliography. `anc/supplement.pdf` is the supplementary
mathematical text cited there. arXiv archives ancillary files with the article
version. No separate arXiv submission is needed. Ancillary files require a TeX
submission; do not upload the article as PDF-only, and do not put TeX source
inside `anc/`. The supplement's editable source is `paper/supplement.tex` in
the repository. Its PDF contains no JavaScript or external attachments.

The upload archive excludes review images, compilation logs, alternate paper
sources, Lean files and historical notes. In arXiv's processing screen, select
`main.tex`, review the compiled PDF and confirm that the ancillary PDF is listed.
Keep the title, authors and category. The comments field can say:
"20 pages; supplementary proofs included as ancillary material."

Official instructions: [ancillary files](https://info.arxiv.org/help/ancillary_files.html)
and [TeX submission](https://info.arxiv.org/help/submit_tex.html).

## Palomar repository structure

The Lean project is at the repository root. Select these paths:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
LICENSE
formalization.yaml
comparator-palomar.json
PalomarPaperChallenge.lean
PalomarPaperSolution.lean
PalomarBridge/                 # statement dictionaries and consistency
PalomarPreservationBridge/
PalomarDCBridge/
PalomarSolovayBridge/
ZFVP/                         # proofs
vendor/Foundation/            # source dependency, with its licence
paper/
  vopenka_without_choice_V3.tex
  vopenka_without_choice_V3.pdf
  supplement.tex
  supplement.pdf
```

Do not submit a ZIP to Palomar. Give the public repository
`Tomodovodoo/vopenka-without-choice`, a full 40-character commit SHA,
`comparator-palomar.json`, and `formalization.yaml`. Leave the project path
empty. This is one entry covering the four selected result families. The
individual configuration files are diagnostic configurations.

The Challenge imports only Mathlib and gives the independent membership,
forcing and real-line vocabulary. The Solution composes the proved dictionaries
with the existing proofs. The paper's fragment-preservation and end-extension
results also have library exports; the combined registry configuration selects
full VP preservation, equiconsistency, the DC consequence and the ordinary-real
Solovay consequence.

`formalization.yaml` cites the paper, supplement and directly used mathematical
sources. Its fidelity and alignment fields explain the construction and
interpretation. Code and documentation use Apache-2.0. The paper and supplement
use CC-BY-4.0 under `paper/LICENSE`. Vendored dependencies retain their notices.

## Verification and intake

The module interfaces and toolchain must satisfy the current Palomar policy.
The project pins Lean 4.35.0-rc2 and the matching Mathlib revision. Run:

```sh
python scripts/generate-palomar-challenge.py --check
python scripts/check-repository.py --config comparator-palomar.json --submission
lake build PalomarPaperChallenge PalomarPaperSolution
bash scripts/verify-protected.sh comparator-palomar.json
```

The protected command needs Linux and bubblewrap. It uses the Comparator,
NanoDa and con-ron bundled with the pinned Lean toolchain. A native Windows
check without bubblewrap is a local diagnostic, not a protected replay.

Run **Palomar mechanical preflight** from GitHub Actions for the exact public
commit. This workflow calls Palomar's pinned reusable verification workflow
with `mode: full` and `execution_profile: palomar-namespace-16x32-v1`. The
combined kernel comparison exceeded the 16 GB hosted worker; this is Palomar's
approved 32 GB profile. The repository needs access to the corresponding
Namespace runner. The workflow runs
automatically for the publication pull request and can be dispatched manually.
The mechanical report must have `status: pass` before intake. A local build or
the repository-specific diagnostic workflow does not replace that report.

Open [Palomar intake](https://submit.palomar-registry.org/). Supply the repository,
commit and paths above. The relationship to the formalization is **maintainer**
for Tom de Groot. The human submitter completes GitHub sign-in. An agent must
not operate that sign-in. Palomar also supports a separate `gh` proof of repository
write access, with confirmation of the exact commit, paths and relationship
before the authentication artifacts are created.

After mechanical verification, read the editorial review. Registration publishes
the source identity and that review permanently. Select registration only after
deciding to publish the displayed review. Save the resulting Palomar identifier.

Official [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [agent/API instructions](https://submit.palomar-registry.org/llms.txt).

## Submission order

Submit the arXiv paper and ancillary supplement first. The citation in the paper
names the supplement accompanying the article, so it needs no prospective
Palomar identifier. The formalization's immutable repository citation is usable
before registry review. Palomar can then cite the announced arXiv version and
the supplement in the exact repository snapshot. Once registered, the Palomar
identifier can be added to the repository and the article metadata or a later
paper revision. The mathematical publication does not need to wait for registry
registration.

The arXiv and Palomar preparations can proceed concurrently. Their final records
have separate versions: an arXiv replacement cannot change a registered Lean
snapshot, and a Palomar registration cannot change the archived supplement.
