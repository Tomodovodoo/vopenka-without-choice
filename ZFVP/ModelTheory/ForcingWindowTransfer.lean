import ZFVP.ModelTheory.ForcingAgreementDensity
import ZFVP.ModelTheory.UniformForcingDefinitions

/-!
# Transfer of satisfaction along a split forcing projection

This is the parametric core of the paper's finite window lemma. Two forcing contexts are
joined by a split projection, the small generic filter is the projection of the big one,
and the forcing sets of the two posets agree along the section `E` for every formula code
of a fixed Levy level. Under those hypotheses a formula of that level holds of a sequence
of ground names in the small extension exactly when it holds in the big one.

The agreement itself is a premise here, bundled as `ForcingLevelAgreement`. It is the
paper's displayed equivalence between forcing over the small poset and forcing over the
big poset, together with the same equivalence for the negation. Nothing about the Woodin
iteration or about endpoints appears in this file.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The two clauses of the paper's forcing agreement, for every formula code of Levy level
`(pol, k)` and every ground sequence of names. `forces` says a small condition `q` forces
`φ` over the small poset exactly when its section `E ‘ q` forces `φ` over the big one;
`refutes` says the same for the negation of the forcing set. This is a hypothesis of the
transfer theorems below, not something proved here. -/
structure ForcingLevelAgreement (P0 R0 P1 R1 E D0 D1 : V) (pol : LevyPolarity) (k : ℕ) :
    Prop where
  forces : ∀ n φ, IsLevyFormulaCode pol k n φ → ∀ b ∈ D0 ^ n, ∀ q ∈ P0,
    q ∈ internalForcingSet P0 R0 D0 n φ b ↔ E ‘ q ∈ internalForcingSet P1 R1 D1 n φ b
  refutes : ∀ n φ, IsLevyFormulaCode pol k n φ → ∀ b ∈ D0 ^ n, ∀ q ∈ P0,
    q ∈ forcingNegation P0 R0 (internalForcingSet P0 R0 D0 n φ b) ↔
      E ‘ q ∈ forcingNegation P1 R1 (internalForcingSet P1 R1 D1 n φ b)

namespace ForcingContext

/-- Truth in the big extension gives truth in the small one. This is the direction that
uses genericity of the big filter: the small conditions forcing `φ` are dense below the
projection of a condition in the big filter. -/
theorem forcingWindow_transfer_of_big
    {A0 A1 : ForcingContext V} {π E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hsplit : IsForcingSplitProjection A0.P A0.R A1.P A1.R π E)
    (hGproj : A0.G = forcingProjectionGeneric A0.P A0.R π A1.G)
    (hD0 : ∀ τ ∈ D0, IsForcingName A0.P τ)
    (hD1 : ∀ τ ∈ D1, IsForcingName A1.P τ)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ)
    {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (range (A1.evaluationGraph D1 hD1)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hD1 hb1)) →
      MembershipSatisfies (range (A0.evaluationGraph D0 hD0)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hD0 hb)) := by
  intro hsat
  refine (A0.levelGenericTruth D0 hD0 hφ b hb).mpr ?_
  rw [hGproj]
  refine agreement_forces_of_generic A0.order hsplit A1.generic
    ((internalForcingSet_regular A1.order hφ.membershipCode hb1).2.1)
    (hagree.refutes n φ hφ b hb) ?_
  exact (A1.levelGenericTruth D1 hD1 hφ b hb1).mp hsat

/-- Truth in the small extension gives truth in the big one. Only the filter property of
the big generic is used: a condition of the small filter has a witness in the big filter
below its section. -/
theorem forcingWindow_transfer_of_small
    {A0 A1 : ForcingContext V} {π E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hsplit : IsForcingSplitProjection A0.P A0.R A1.P A1.R π E)
    (hGproj : A0.G = forcingProjectionGeneric A0.P A0.R π A1.G)
    (hD0 : ∀ τ ∈ D0, IsForcingName A0.P τ)
    (hD1 : ∀ τ ∈ D1, IsForcingName A1.P τ)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ)
    {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (range (A0.evaluationGraph D0 hD0)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hD0 hb)) →
      MembershipSatisfies (range (A1.evaluationGraph D1 hD1)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hD1 hb1)) := by
  intro hsat
  refine (A1.levelGenericTruth D1 hD1 hφ b hb1).mpr ?_
  refine agreement_generic_of_forces hsplit A1.generic.1
    ((internalForcingSet_regular A1.order hφ.membershipCode hb1).2.1)
    (hagree.forces n φ hφ b hb) ?_
  have := (A0.levelGenericTruth D0 hD0 hφ b hb).mp hsat
  rwa [hGproj] at this

/-- Satisfaction transfer across the window. A formula code of Levy level `(pol, k)` holds
of a sequence of ground names in the small extension exactly when it holds in the big one.
The proof rewrites both sides by the truth lemma of the two contexts and then applies the
agreement equivalence for generic filters. -/
theorem forcingWindow_transfer
    {A0 A1 : ForcingContext V} {π E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hsplit : IsForcingSplitProjection A0.P A0.R A1.P A1.R π E)
    (hGproj : A0.G = forcingProjectionGeneric A0.P A0.R π A1.G)
    (hD0 : ∀ τ ∈ D0, IsForcingName A0.P τ)
    (hD1 : ∀ τ ∈ D1, IsForcingName A1.P τ)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ)
    {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (range (A0.evaluationGraph D0 hD0)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hD0 hb)) ↔
      MembershipSatisfies (range (A1.evaluationGraph D1 hD1)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hD1 hb1)) := by
  rw [A0.levelGenericTruth D0 hD0 hφ b hb, A1.levelGenericTruth D1 hD1 hφ b hb1, hGproj]
  exact genericMeets_agreement_iff A0.order A1.order hsplit A1.generic
    (internalForcingSet_subset _ _ _ _ _ _)
    ((internalForcingSet_regular A1.order hφ.membershipCode hb1).2.1)
    (hagree.forces n φ hφ b hb) (hagree.refutes n φ hφ b hb)

/-- The same transfer when the small name set is contained in the big one, so that a
sequence of small names is automatically a sequence of big names. -/
theorem forcingWindow_transfer_of_subset
    {A0 A1 : ForcingContext V} {π E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hsplit : IsForcingSplitProjection A0.P A0.R A1.P A1.R π E)
    (hGproj : A0.G = forcingProjectionGeneric A0.P A0.R π A1.G)
    (hD0 : ∀ τ ∈ D0, IsForcingName A0.P τ)
    (hD1 : ∀ τ ∈ D1, IsForcingName A1.P τ)
    (hsub : D0 ⊆ D1)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ)
    {b : V} (hb : b ∈ D0 ^ n) :
    MembershipSatisfies (range (A0.evaluationGraph D0 hD0)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hD0 hb)) ↔
      MembershipSatisfies (range (A1.evaluationGraph D1 hD1)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hD1
          (mem_function_of_mem_function_of_subset hb hsub))) :=
  forcingWindow_transfer hsplit hGproj hD0 hD1 hagree hφ hb
    (mem_function_of_mem_function_of_subset hb hsub)

end ForcingContext

end ZFVP
