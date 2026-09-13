# Ordinary-real Solovay consistency

[TheoremSolovay.lean](TheoremSolovay.lean) proves
`HasZFVPModel → HasSolovayModel`. Its model-existence equivalence identifies the
target with the complete existing `realSolovayTheory` consistency statement.

The target includes ZF, full VP, DC, failure of AC, Lebesgue measurability, the
Baire property and the perfect set property for every internal set of ordinary
reals, and an omega-one-complete nonprincipal ultrafilter on omega one.

The statement uses [the shared membership vocabulary](../PalomarBridge/Vocabulary.lean)
and [explicit DC](../PalomarDCBridge/Vocabulary.lean). The remaining definitions
are in [Vocabulary.lean](Vocabulary.lean). No regularity predicate is an
unspecified parameter, and the bridge introduces no countability assumption.

| Module | Correspondence proved |
| --- | --- |
| [ArithmeticDictionary](ArithmeticDictionary.lean) | Internal recursion, natural and signed arithmetic, rational quotients and rational order. |
| [RegularityDictionary](RegularityDictionary.lean) | Real cuts, measure and topological definitions, and LM/BP/PSP. |
| [TargetDictionary](TargetDictionary.lean) | Hartogs omega one, the complete nonprincipal ultrafilter, and universal regularity clauses. |
| [TheoremSolovay](TheoremSolovay.lean) | Full source-theory equivalence and composition with the existing Solovay consistency theorem. |

The dictionary proofs depend on the preceding rows. The final theorem also
uses the completed shared ZF/VP and DC dictionaries. The arithmetic and regularity
proofs in the original project are reused.

[ExportChecks.lean](ExportChecks.lean), the [check output](../verification/solovay-bridge-check.txt)
and [source receipt](../verification/solovay-bridge-check.json) record the local
Lean checks. The root generated Challenge and Solution are selected by
[comparator-palomar-solovay.json](../comparator-palomar-solovay.json).
