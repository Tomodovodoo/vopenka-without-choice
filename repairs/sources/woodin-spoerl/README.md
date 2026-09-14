# Woodin and Spoerl

Sources: Woodin, [*Suitable extender models I*](https://doi.org/10.1142/S021906131000095X), Theorem 226, printed pages 322–326; Spoerl, [*Cardinals Beyond Choice and the HOD-Dichotomy*](https://diposit.ub.edu/bitstreams/7cf6497e-0aef-4e41-bc1c-a84ef0aa63f0/download), Definition 43, Theorem 44 and Lemma 45. The source references and bibliography also appear in the [original manuscript](../../../paper/Vopenkas_Principle_Without_Choice_final.tex).


## Iteration seed

Woodin, proof of Theorem 226, p. 323.

The chosen initial cutoff and the lower parameter of the first collapse need not agree. The inductive invariant cannot be assumed at the initial stage.

Placement: correct or justify the seed in Woodin's construction first. Our Theorem 5.5 should identify the convention it uses and cite the source supplement. V13 starts with the trivial stage and the least DC-failure cutoff, then collapses at the first successor. [Why this placement](../../placement.md#w1-initial-collapse).

Lean: [WoodinConstruction](../../../ZFVP/ModelTheory/WoodinConstruction.lean).

[Detailed argument](proofs/woodin_paper_theorem_proof.md).

## Raw inverse limits and completed stages

Woodin, Theorem 226, pp. 323–324; Spoerl, Definition 43 and Theorem 44.

The raw inverse limit and the stage obtained after its appended collapse have different cutoffs. Mixing these conventions loses the premises needed for DC and regularity.

Placement: put the comparison and the DC argument in a source-construction supplement, then identify the adopted convention in our paper. Different conventions alone do not refute either construction. [Why this placement](../../placement.md#w2-raw-inverse-stage-completed-stage-and-dc-bound).

Lean: [WoodinRawInverseDC](../../../ZFVP/ModelTheory/WoodinRawInverseDC.lean).

[Detailed argument](proofs/woodin_inverse_limit_dependent_choice.md).

## The restricted lift

Spoerl, Lemma 45, pp. 26–27; original paper, Theorem 5.5, clause 3.

Agreement at Vγ does not imply agreement at Vγ+1. A later collapse can add subsets of Vγ. The asserted successor-rank inference for that same embedding therefore needs an additional argument.

Placement: the missing justification belongs in Spoerl's lifting proof. Our theorem can cite the restricted replacement on marked final ranks with the whole captured forcing code. This supplies the downstream input but does not repair the full source assertion. Choosing a taller embedding can provide a different route; it does not validate the original same-embedding inference. [Why this placement](../../placement.md#w3-lifting-to-the-final-successor-ranks).

Lean: [WoodinSparseActualCriticalLift](../../../ZFVP/ModelTheory/WoodinSparseActualCriticalLift.lean), [WoodinSparseSourceRelativeHomogeneity](../../../ZFVP/ModelTheory/WoodinSparseSourceRelativeHomogeneity.lean).

[Detailed argument](proofs/w04-restricted-lift-bridge.md).

## Ambient HOD remains separate

Woodin, Theorem 226, clause 3, p. 326.

Σ₃ definability alone does not transfer the claimed Σ₂ correctness to the extension. Bounded HOD stabilization also does not place the chosen source rank beyond stabilization or identify ambient HOD with internal HOD.

Placement: retain this as an unresolved source-proof issue for author review. The current paper route avoids this clause. Do not claim the theorem false, or advertise the complete ambient-HOD assertion as a Lean theorem. The modules below supply parts of the alternative finite-restoration route, not a proof of clause 3.

Lean: [WoodinSparseFiniteReflection](../../../ZFVP/ModelTheory/WoodinSparseFiniteReflection.lean), [WoodinSparseRestorationTheorem](../../../ZFVP/ModelTheory/WoodinSparseRestorationTheorem.lean).

[Detailed argument](proofs/woodin_ambient_hod_stabilization.md).
