# VopÄ›nkaâ€™s principle without Choice

Lean formalization of *VopÄ›nkaâ€™s Principle without Choice: Preservation under
Symmetric Extensions*, with its supporting mathematical arguments.

[Paper PDF](paper/vopenka_without_choice_V3.pdf) Â·
[Supplement PDF](paper/supplement.pdf) Â·
[arXiv article](https://arxiv.org/abs/2609.06856) Â·
[Submission instructions](docs/submission.md)

The library proves symmetric preservation, same-level fragment preservation,
equiconsistency of ZF+VP and ZFC+VP, and the stated model-construction
consequences. The paper uses a completed Woodin iteration, a marked-rank lift,
finite definability bounds and induced-generic endpoint truth. The supplement
states the supporting arguments and the correspondence with the formal exports.

## Build and verification

Install the pinned Lean toolchain with elan, then run:

```sh
lake exe cache get
lake build ZFVP PalomarPaperChallenge PalomarPaperSolution
```

The project pins Lean 4.35.0-rc2 and its matching Mathlib revision. Foundation is
included as source with its compatibility changes and licence. Dependency
builds belong to this checkoutâ€™s own `.lake` directory.

[Verification records](docs/verification.md) identify the exact source snapshots
and checks. The [Palomar setup](docs/palomar.md) describes the four selected
principal result families and their independent statements. Palomar intake
requires its complete reusable mechanical preflight for the submitted commit.

## Publication files

`paper/vopenka_without_choice_V3.tex` is the article source and
`paper/supplement.tex` is the companion mathematical text. The articleâ€™s
bibliography cites the supplement by section and theorem. Run
`python scripts/package-publication.py` to create the arXiv source archive.

The Lean files, statement dictionaries, sources, metadata and Comparator
configuration remain at the repository root. One Palomar configuration,
`comparator-palomar.json`, selects full symmetric VP preservation,
equiconsistency, the DC consequence and the ordinary-real Solovay consequence.
The additional library exports remain available from the same source snapshot.

Code and documentation use Apache-2.0. The article and supplement use CC-BY-4.0
under [paper/LICENSE](paper/LICENSE). Dependencies retain their licences and
copyright notices. [Dependency provenance](docs/provenance.md).
