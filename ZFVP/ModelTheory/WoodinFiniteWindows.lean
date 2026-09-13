import ZFVP.ModelTheory.ForcingWindowTransfer
import ZFVP.ModelTheory.WoodinEndpointForcing
import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.SetTheory.Cn

/-! # The finite window lemma at two Woodin endpoints

This is the Lean form of the paper's `lem:finite-windows`: if `θ < Λ` are supercompact in
Woodin's choiceless sense, Woodin's iteration is defined through `Λ`, and `θ, Λ ∈ C^(r_k)`,
then for a `Q_Λ`-generic `G` the rank segment `(V[G])_θ` is a `Σ_k`-elementary submodel of
`(V[G])_Λ`.  The paper's `r_k` is `uniformForcingLevelBound pol k`, the Levy bound of the
uniform endpoint forcing formula.

Nothing about the iteration is proved here.  Following the frozen W02 boundary, everything
the argument needs from the neighbouring work packages is a named hypothesis:

* W02, the construction itself, enters as `WoodinIterationConstruction (V := V)` together
  with `¬InternalChoice V`.  It is carried on the statements, never assumed silently.
* W03, the marked-stage identification `V_θ[G_θ] = (V[G])_θ` and its counterpart at `Λ`,
  enters as the two `smallRank` and `bigRank` fields of `WoodinWindowData`.  It cannot be
  derived from `ForcingContext.lowRankEvaluation_range` here, since that lemma wants the
  poset to sit inside `V_θ`, which fails for the endpoint forcing.
* W04, the endpoint comparison, enters as the `split` and `projected` fields: the complete
  embedding of `Q_θ` into `Q_Λ` presented as a split projection, and `G_θ = G ∩ Q_θ`.
* The forcing agreement of the paper's displayed equation, together with its negation
  clause, enters as `ForcingLevelAgreement`.

Given those, the transfer is `ForcingContext.forcingWindow_transfer` after rewriting the
two rank sets by the marked-stage identities.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- What W03 and W04 owe the window lemma at the pair of endpoints `θ < Λ`.

`smallPoset`, `smallOrder`, `bigPoset`, `bigOrder` say the two forcing contexts are the
endpoint forcings `Q_θ` and `Q_Λ`.  `split` and `projected` are the W04 endpoint comparison:
the complete embedding of `Q_θ` into `Q_Λ` as a split projection with section `E`, and the
induced generic `G_θ = G ∩ Q_θ`.  `smallNames` and `bigNames` say the two name sets consist
of names for the respective posets.  `smallRank` and `bigRank` are the W03 marked-stage
identifications: evaluating the names of `D0` gives exactly `(V[G])_θ`, and likewise at `Λ`. -/
structure WoodinWindowData (θ Λ : V) (A0 A1 : ForcingContext V) (π E D0 D1 : V) : Prop where
  smallPoset : A0.P = woodinEndpointPoset θ
  smallOrder : A0.R = woodinEndpointOrder θ
  bigPoset : A1.P = woodinEndpointPoset Λ
  bigOrder : A1.R = woodinEndpointOrder Λ
  split : IsForcingSplitProjection A0.P A0.R A1.P A1.R π E
  projected : A0.G = forcingProjectionGeneric A0.P A0.R π A1.G
  smallNames : ∀ τ ∈ D0, IsForcingName A0.P τ
  bigNames : ∀ τ ∈ D1, IsForcingName A1.P τ
  smallRank : range (A0.evaluationGraph D0 smallNames) = hierarchy (A0.check θ)
  bigRank : range (A1.evaluationGraph D1 bigNames) = hierarchy (A1.check Λ)

/-- The finite window lemma.  For a formula code of Levy level `(pol, k)` and a sequence of
ground names, truth in `(V[G])_θ` and truth in `(V[G])_Λ` agree.  Quantifying over all such
codes and sequences, this is the paper's `(V[G])_θ ≺_{Σ_k} (V[G])_Λ`. -/
theorem woodin_finite_windows
    (hcon : WoodinIterationConstruction (V := V)) (hAC : ¬InternalChoice V)
    {θ Λ : V} (hθ : IsWoodinSupercompact θ) (hΛ : IsWoodinSupercompact Λ) (hθΛ : θ ∈ Λ)
    {pol : LevyPolarity} {k : ℕ}
    (hθC : Cn (uniformForcingLevelBound pol k) θ) (hΛC : Cn (uniformForcingLevelBound pol k) Λ)
    {A0 A1 : ForcingContext V} {π E D0 D1 : V}
    (hdata : WoodinWindowData θ Λ A0 A1 π E D0 D1)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ) {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (hierarchy (A0.check θ)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hdata.smallNames hb)) ↔
      MembershipSatisfies (hierarchy (A1.check Λ)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hdata.bigNames hb1)) := by
  rw [← hdata.smallRank, ← hdata.bigRank]
  exact ForcingContext.forcingWindow_transfer hdata.split hdata.projected
    hdata.smallNames hdata.bigNames hagree hφ hb hb1

/-- The density half of the paper proof: a level-`k` truth in `(V[G])_Λ` comes back down to
`(V[G])_θ`.  The conditions of `Q_θ` forcing the code are dense below the restriction of a
condition of `G`, so genericity of `G` produces one in `G_θ`. -/
theorem woodin_finite_windows_of_big
    (hcon : WoodinIterationConstruction (V := V)) (hAC : ¬InternalChoice V)
    {θ Λ : V} (hθ : IsWoodinSupercompact θ) (hΛ : IsWoodinSupercompact Λ) (hθΛ : θ ∈ Λ)
    {pol : LevyPolarity} {k : ℕ}
    (hθC : Cn (uniformForcingLevelBound pol k) θ) (hΛC : Cn (uniformForcingLevelBound pol k) Λ)
    {A0 A1 : ForcingContext V} {π E D0 D1 : V}
    (hdata : WoodinWindowData θ Λ A0 A1 π E D0 D1)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ) {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (hierarchy (A1.check Λ)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hdata.bigNames hb1)) →
      MembershipSatisfies (hierarchy (A0.check θ)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hdata.smallNames hb)) := by
  rw [← hdata.smallRank, ← hdata.bigRank]
  exact ForcingContext.forcingWindow_transfer_of_big hdata.split hdata.projected
    hdata.smallNames hdata.bigNames hagree hφ hb hb1

/-- The filter half of the paper proof: a level-`k` truth in `(V[G])_θ` goes up to
`(V[G])_Λ`.  Only the filter property of `G` is used, through the section of a condition of
`G_θ`. -/
theorem woodin_finite_windows_of_small
    (hcon : WoodinIterationConstruction (V := V)) (hAC : ¬InternalChoice V)
    {θ Λ : V} (hθ : IsWoodinSupercompact θ) (hΛ : IsWoodinSupercompact Λ) (hθΛ : θ ∈ Λ)
    {pol : LevyPolarity} {k : ℕ}
    (hθC : Cn (uniformForcingLevelBound pol k) θ) (hΛC : Cn (uniformForcingLevelBound pol k) Λ)
    {A0 A1 : ForcingContext V} {π E D0 D1 : V}
    (hdata : WoodinWindowData θ Λ A0 A1 π E D0 D1)
    (hagree : ForcingLevelAgreement A0.P A0.R A1.P A1.R E D0 D1 pol k)
    {n φ : V} (hφ : IsLevyFormulaCode pol k n φ) {b : V} (hb : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n) :
    MembershipSatisfies (hierarchy (A0.check θ)) (A0.check n) (A0.check φ)
        (A0.sequenceValue b (A0.nameSequence_of_mem_function hdata.smallNames hb)) →
      MembershipSatisfies (hierarchy (A1.check Λ)) (A1.check n) (A1.check φ)
        (A1.sequenceValue b (A1.nameSequence_of_mem_function hdata.bigNames hb1)) := by
  rw [← hdata.smallRank, ← hdata.bigRank]
  exact ForcingContext.forcingWindow_transfer_of_small hdata.split hdata.projected
    hdata.smallNames hdata.bigNames hagree hφ hb hb1

end ZFVP
