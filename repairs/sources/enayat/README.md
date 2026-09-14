# Enayat's Rubin construction

Source: Ali Enayat, [*Models of Set Theory: Extensions and Dead-ends*, v7](https://arxiv.org/abs/2406.14790v7), Definitions 5.10 and 5.13, Theorems 5.15 and 5.18, and the appendix. Our Proposition 9.7 imports Theorem 5.18. V13 should cite a repaired construction rather than leave that import unexplained.

Recommended placement: keep a short statement of the corrected input beside Proposition 9.7, with the detailed repair in a separate source-paper note. These are proposed repairs, not an approved erratum. The existence theorem now used is linked at the end.

The repair belongs primarily to Enayat's definitions and Appendix. Our citation of Theorem 5.18 is a downstream dependency, not the origin of these defects. [Arguments E1–E7](../../placement.md#enayat) explain the placement separately for every item and distinguish the checked ZF-model application from the source's broader arbitrary-language formulations.


## Coded classes versus definable classes

Definition 5.13(b) and the literal formulation of Theorem 5.15.

Coding every relevant class filter as a member produces a set of all ordinals when applied to the cofinal ordinal filter from clause a. That literal formulation contradicts ZF.

Replace class member-coding with parametric definability. For filters on an internal set Fin(a,2), Separation then recovers the required member-code.

Lean: [RubinDefinableFilters](../../../ZFVP/ModelTheory/RubinDefinableFilters.lean).

[Detailed argument](proofs/enayat-internal-rubin-proof.md).

## Which maximality is needed

Definition 5.10(c), footnote 30, appendix Stage 1, p. 25.

An inclusion-maximal directed filter need not contain every point compatible with all its members. The proof uses this stronger property.

Use maximal compatibility; prove the required equivalence for internal finite partial functions.

Lean: [MaximallyCompatibleFilters](../../../ZFVP/ModelTheory/MaximallyCompatibleFilters.lean), [RubinDefinableFilters](../../../ZFVP/ModelTheory/RubinDefinableFilters.lean).

## Block consistency

Appendix claims A3 and A4, p. 26.

Alternating bounds and witnesses do not express simultaneous cofinal realizability. With even and odd directed sets and d₂<d₁, a later bound can defeat an already chosen first witness.

Use one block of universal bounds followed by one block of existential witnesses. This is the consistency equivalence needed by the upper-bound theory.

Lean: [AlternatingBlocks](../../../ZFVP/ModelTheory/AlternatingBlocks.lean), [RubinBlockLemmas](../../../ZFVP/ModelTheory/RubinBlockLemmas.lean).

## Separating types

Appendix claim A5, pp. 26–27.

The eventual bound can depend on x. This does not refute a block-existential assertion with varying x, and the final contradiction omits the θ conjunct.

Omit the type over the full upper-bound theory. Keep θ and the negated candidate definition together under the common witness tuple.

Lean: [SchmerlInternalRubinConstruction](../../../ZFVP/ModelTheory/SchmerlInternalRubinConstruction.lean).

[Detailed argument](proofs/enayat-internal-rubin-proof.md).

## Branch preservation

Appendix claim A7, p. 28.

Nodes possible below different extensions of a condition need not lie on one branch. Cofinal occurrence alone does not make their union a chain.

Use square ccc to bound the ranks of splitting pairs. Densely find a condition whose remaining possibilities form an old branch. This repair uses the specific product hypotheses, not a claim that every ccc product is ccc.

Lean: [SchmerlBranchPreservation](../../../ZFVP/ModelTheory/SchmerlBranchPreservation.lean), [SchmerlSpecializationProducts](../../../ZFVP/ModelTheory/SchmerlSpecializationProducts.lean).

[Detailed argument](proofs/e10-e12-schmerl-route-repair.md).

## Return to the original language

Appendix Stage 2, Step 2, p. 29.

A definition in the language expanded by the specializing coloring need not define the class in the original membership reduct.

Use original-language definitions and codes for the full generated filters before taking the reduct.

Lean: [SchmerlCodedWeaklyRubinRealization](../../../ZFVP/ModelTheory/SchmerlCodedWeaklyRubinRealization.lean).

[Detailed argument](proofs/e10-e12-schmerl-route-repair.md).

## Cover every internally finite domain

Appendix Stage 2, Step 1, p. 27, and extraction on p. 29.

An internally finite domain can be externally infinite. Selected-domain branches do not automatically cover every such domain.

Add FinSmall: each internally finite set has externally countable member trace. Preserve old finite sets by omission and use the explicit Q-smallness condition in extraction. The strengthened existence theorem supplies this premise.

Lean: [SchmerlInternalRubinConstruction](../../../ZFVP/ModelTheory/SchmerlInternalRubinConstruction.lean), [SchmerlNamedConsistency](../../../ZFVP/ModelTheory/SchmerlNamedConsistency.lean).

[Detailed argument](proofs/e05-finite-domain-coverage-repair.md).

The repaired existence export is `exists_alephOneWeaklyRubinExtension` in [SchmerlNamedConsistency](../../../ZFVP/ModelTheory/SchmerlNamedConsistency.lean). The full mathematical construction is in [the internal Rubin proof](proofs/enayat-internal-rubin-proof.md).
