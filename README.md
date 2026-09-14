# Vopěnka's principle without choice

Lean formalization and proposed proof repairs for *Vopěnka's Principle without Choice: Preservation under Symmetric Extensions*, by Tom de Groot and Wojciech Aleksander Wołoszyn.

[Original paper on arXiv](https://arxiv.org/abs/2609.06856v1) · [Original manuscript](paper/Vopenkas_Principle_Without_Choice_final.pdf) · [V13 working revision](paper/vopenka_without_choice_V13.pdf)

## Results and remaining gaps

The formalized routes cover symmetric preservation, Theorem A; the equiconsistency conclusion, Theorem B; the arbitrary-ground Cohen application with a supplied generic; and the ordinary-real Solovay conclusion. The publication checkout's local full build completed 5,076 jobs. Both four-result configurations passed protected Comparator and NanoDa. See [verification and its limits](docs/verification.md).

V13 still states two auxiliary clauses broader than the matching Lean exports: a sharp Σ₃ bound for its specified sparse Woodin presentation, and endpoint forcing truth with its full endpoint and class-generic quantifiers. [Exact statements, available proofs and ways to close the differences](repairs/formalization/README.md). These differences must be resolved before describing every clause of V13 as formalized.

## Where to find the repairs

* [Repair index](repairs/README.md): source-paper issues, their consequences, and proposed placement.
* [Where each repair belongs](repairs/placement.md): individual arguments for source corrections, downstream citation changes, and formalization-only work.
* [Consequences for our manuscript](repairs/our-paper/README.md): which source repairs need a citation or changed input, and which additions are proof details.
* [Woodin and Spoerl](repairs/sources/woodin-spoerl/README.md): iteration conventions, restricted lifting, and the separate unresolved ambient-HOD clause.
* [Enayat](repairs/sources/enayat/README.md): Rubin definitions, block quantifiers, branch preservation, and finite-domain coverage.
* [Other cited results](repairs/sources/other/README.md): rank-Berkeley's zero case, same-extension generics, and clarification of imported results.
* [Rejected formalization routes](repairs/development/README.md): failed intermediate claims that should not be attributed to the cited authors.

Each entry links to Lean source and, where available, a detailed mathematical argument. A proposed correction here is not an author-approved erratum. Unresolved source arguments are distinguished from counterexamples to literal statements.

## Build

[Palomar and Comparator setup](docs/palomar.md) · [Documentation index](docs/README.md)

[comparator-palomar.json](comparator-palomar.json) selects all four principal
result families in one standalone statement for one Palomar entry. Its vocabulary
imports only mathlib; proved dictionaries connect it to the existing proofs.
The [setup account](docs/palomar.md) links each bridge and the submission gates.

Individual configurations remain available for diagnosis. `comparator.json`
also checks the four results in their original Foundation encoding. That
configuration is outside Palomar's Challenge import policy.

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build ZFVP
```

The toolchain is Lean `v4.34.0-rc2`. The manifest pins mathlib and its transitive dependencies. Foundation is included as source, with the local compatibility changes already applied. Do not replace it with an unpatched upstream checkout. The first build needs network access for dependencies.

`ZFVP.lean` is the main import target. `ZFVP/ModelTheory` contains model constructions and forcing applications; `ZFVP/SetTheory` contains their internal set-theoretic statements. Additional source modules include supporting and optional results. Presence in the repository alone does not establish correspondence with a paper statement.

## Manuscripts and licensing

The original manuscript and V13 are preserved as separate files. The repair notes propose further edits; they do not silently alter either manuscript. External source papers are linked rather than redistributed. See [dependency provenance and licensing](docs/provenance.md).
