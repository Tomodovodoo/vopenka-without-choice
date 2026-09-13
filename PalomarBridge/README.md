# Independent statement of Theorem B

The statement vocabulary in [Vocabulary.lean](Vocabulary.lean) imports only Mathlib.
The proof [independent_theoremB](TheoremB.lean) establishes
`HasZFCVPModel ↔ HasZFVPModel` and identifies both sides with the original
proof-theoretic consistency statements.

The root Palomar Challenge and Solution are separate modules. The Challenge
must contain the vocabulary itself, because Palomar does not allow a local
project import in its transitive import closure. Proof-side modules may import
this vocabulary and the existing Foundation/ZFVP development.

## Meaning of the statement

- ZF includes every parameter instance of separation and replacement.
- VP concerns every internal set-sized signature and every parameter-definable
  proper class of its internal structures.
- Elementary embeddings are internal graphs preserving every internally finite
  formula. Nonstandard formulas are retained in nonstandard models.
- Model domains need not be externally countable or well-founded.
- The set and recursion operations are specified by explicit membership or
  recursion equations. Their correspondence proofs establish existence and
  uniqueness wherever the VP definition uses them. No unspecified predicate
  or operation is supplied by a Comparator definition hole.

## Proof dependencies

| Module | What it proves |
| --- | --- |
| [FoundationTranslation](FoundationTranslation.lean) | Inverse translations of membership syntax, preservation of satisfaction, and the model-existence/consistency equivalence. |
| [ZFDictionary](ZFDictionary.lean) | Full ZF and AC correspondence, including both parameterized axiom schemes. |
| [CodingOperations](CodingOperations.lean) | Agreement of the explicitly defined set operations with Foundation. |
| [InternalSyntaxDictionary](InternalSyntaxDictionary.lean) | Agreement of internal languages, structures, and least closed term/formula sets. |
| [InternalEvaluationDictionary](InternalEvaluationDictionary.lean) | Agreement of internal term-evaluation graphs and atomic satisfaction. |
| [VPDictionary](VPDictionary.lean) | Agreement of the internal truth graph, elementary embeddings, and full VP scheme. |
| [TheoremB](TheoremB.lean) | Composition with the existing Woodin consistency theorem, yielding the independent theorem statement. |

Each row depends on the preceding row. The final row also imports the existing
[Woodin theorem](../ZFVP/ModelTheory/WoodinSparseRestorationTheorem.lean).
The translation uses equality normalization and completeness, not an assumption
that the starting model is transitive or countable.

## Why shared definitions are needed

The existing formula for coded elementary embeddings expands to 7,983,105
formula nodes. A VP instance with a false class formula expands to 7,992,560.
Writing that tree literally cannot meet Palomar's Challenge size limit.
The shared semantic definitions retain the same internal coding and recursion
while keeping the statement readable and within the limit.

These are statement-translation changes. They do not alter Theorem B or claim
to settle the two separately recorded auxiliary manuscript-scope gaps.

