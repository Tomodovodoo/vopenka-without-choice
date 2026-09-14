# Other cited inputs


## Exclude the zero rank-Berkeley case

Mohammd, [*Berkeley Cardinals and Vopěnka's Principle*](https://arxiv.org/abs/2404.10455), Definition 4.4; our definition before Lemma 5.2.

At δ=0 the literal quantified clause is vacuous. Its unrestricted existence assertion is then automatic, defeating the intended no-rank-Berkeley pruning case.

Placement: make the boundary convention explicit in Mohammd's definition and in our repeated definition, which is negated in pruning. This shared definition requires the change in both places. It does not refute the intended positive-cardinal theorem. [Placement argument](../../placement.md#m1-the-zero-rank-berkeley-case).

Lean: [RankBerkeley](../../../ZFVP/SetTheory/RankBerkeley.lean), [PrunedUnboundedExtendibility](../../../ZFVP/ModelTheory/PrunedUnboundedExtendibility.lean).

[Detailed argument](proofs/rank_berkeley_nonzero_correction.md).

## Quantify over generics giving the same extension

Karagila and Schilhan, [*Towards a theory of symmetric extensions*, v1](https://arxiv.org/abs/2602.17338v1), Proposition 9.4, reverse inclusion, p. 33; our Lemma 8.4.

A comparison generic H lying in V[G] need not satisfy V[H]=V[G]. Lemma 9.3 requires that equality.

Placement: repair the reverse-inclusion proof of Proposition 9.4 in the source paper, then cite that repaired input in our Solovay application. Restrict comparison generics definably using a ground set of canonical names for all subsets of the Boolean algebra. This ensures recovery of G without using G as a defining parameter. The linked Lean route covers our application; it does not certify every class-name case of the source proposition. [Placement argument](../../placement.md#k1-comparison-generics-must-generate-the-same-extension).

Lean: [SolovayOrbitDefinable](../../../ZFVP/ModelTheory/SolovayOrbitDefinable.lean), [SolovayCorollaryUnconditional](../../../ZFVP/ModelTheory/SolovayCorollaryUnconditional.lean), [LevyHighConeTransfer](../../../ZFVP/ModelTheory/LevyHighConeTransfer.lean).

## Spell out the Solovay import

Solovay, the regularity construction in III.1.3–III.1.11 and sequence closure in III.2.4–III.2.11; our Lemma 8.1.

A bare reference to Theorem 1 hides the passage to arbitrary ground-set parameters and full HOD, and the transport from coded reals to the ordinary real line.

Placement: expand our proof, as V13 does, and cite the component arguments. No defect in Solovay's theorem is asserted.

Lean: [SolovayHODRegularity](../../../ZFVP/ModelTheory/SolovayHODRegularity.lean), [RealLebesgueTransfer](../../../ZFVP/SetTheory/RealLebesgueTransfer.lean), [RealSolovayRegularity](../../../ZFVP/ModelTheory/RealSolovayRegularity.lean), [RealSolovayConsistency](../../../ZFVP/ModelTheory/RealSolovayConsistency.lean).

[Detailed argument](proofs/r18-real-measure-proof.md).

## Use Bagaria at the required complexity

Bagaria, C(n)-cardinals, Theorem 4.11; our Theorem 5.13.

The application must include parameters, the correct complexity shift and distinct source and target structures.

Placement: explain in our proof that the Π(N+1) class is used as a Σ(N+2) class; choose κ above the parameters and the source outside Hκ. This is an application detail, not a source correction.

Lean: [WoodinSparseRestorationTheorem](../../../ZFVP/ModelTheory/WoodinSparseRestorationTheorem.lean).

## Supply the class-forcing construction

Usuba, Corollary 4.5 as cited in our Corollary 4.4.

Local collapse alone does not establish global pretameness, tail bounds or stabilization.

Placement: keep the proof details in our formalization supplement. Use common-head reheading, Collection after collapse and limits of Löwenheim–Skolem cardinals above the forcing rank. No source error is asserted.

Lean: [UsubaLSClassRestoration](../../../ZFVP/ModelTheory/UsubaLSClassRestoration.lean), [UsubaForcingDerivability](../../../ZFVP/ModelTheory/UsubaForcingDerivability.lean).

[Detailed argument](proofs/c03-pretameness-and-stabilization-proof.md).
