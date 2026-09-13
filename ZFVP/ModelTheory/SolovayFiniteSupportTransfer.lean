import ZFVP.ModelTheory.SolovayOrbitDefinable

/-! The orbit transfer statement only ever gets used on finite sequences of nice names.

`ZFVP.ForcingContext.groundRealDefinable_booleanReal_of_transfer` assumes
`∀ s k : V, A.OrbitTransfer Pf s k p`, for arbitrary sets `s` and `k`. Its proof picks a finite
support `E` of the symmetric name, enumerates `E` as a finite sequence `s` of length `n ∈ ω`, and
applies the assumption once, as `htr s n`. So the sequence it feeds in is a function with domain a
natural number whose values are all nice names.

This module redoes that chain with the assumption restricted to exactly those `s` and `n`. The
three theorems here have the same conclusions as their counterparts in `SolovayOrbitDefinable`,
with the four side conditions `n ∈ ω`, `IsFunction s`, `domain s = n` and "every `s ‘ i` is a nice
name" added to the transfer hypothesis. Everything downstream of the transfer statement therefore
only has to be established for finite sequences of nice names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-- The value of a hereditarily symmetric name of the Solovay system is definable in the
extension from ground sets, reals and ordinals, given the transfer statement for finite sequences
of nice names. This is `groundRealDefinable_booleanReal_of_transfer` with the transfer hypothesis
restricted to the sequences its proof actually uses. -/
theorem groundRealDefinable_booleanReal_of_finite_transfer (Pf : SetTheorySemisentence 2)
    {p : A.Model} (hp : A.IsGroundRealDefinable p)
    (hground : ∀ a : V, Pf.Evalb ![A.check a, p])
    (htr : ∀ s n : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ i ∈ n, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i)) →
      A.OrbitTransfer Pf s n p)
    (τ : A.solovayContext.Name) :
    A.IsGroundRealDefinable (A.booleanReal ⟨τ.val, τ.property.1⟩) := by
  obtain ⟨E, hEf, hE, hEs⟩ := A.solovay_exists_support τ
  obtain ⟨s, hsfin, hsrange⟩ := exists_finiteSequence_range hEf
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff E s).mp hsfin
  have hsf : IsFunction s := IsFunction.of_mem hsn
  have hsdom : domain s = n := domain_eq_of_mem_function hsn
  have hnω : n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive n hn
  have hsval : ∀ i ∈ n, s ‘ i ∈ E := by
    intro i hi
    rw [← hsrange]
    exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi))
  have hs : ∀ i ∈ n, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i) :=
    fun i hi ↦ (hE _ (hsval i hi)).nice
  have hsym : forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        τ.val := by
    rw [hsrange]
    exact hEs
  set τ' : ForcingName A.booleanContext.P := ⟨τ.val, τ.property.1⟩ with hτ'
  have hsub1 : A.booleanReal τ' ⊆ A.solovayOrbitUnion Pf s n τ.val p :=
    A.booleanReal_subset_solovayOrbitUnion hsdom τ' hs Pf hground
  have hsub2 : A.solovayOrbitUnion Pf s n τ.val p ⊆ A.booleanReal τ' :=
    A.solovayOrbitUnion_subset_booleanReal Pf hsdom τ' hsym (htr s n hn hsf hsdom hs)
  have heq : A.booleanReal τ' = A.solovayOrbitUnion Pf s n τ.val p :=
    mem_ext (fun z ↦ ⟨fun h ↦ hsub1 z h, fun h ↦ hsub2 z h⟩)
  rw [heq]
  exact A.groundRealDefinable_solovayOrbitUnion Pf s τ.val hnω hp

end ForcingContext

/-! ### The pointwise hypothesis of the Solovay corollary -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The hypothesis `hpt` of `solovay_corollary_final`, from the transfer statement of Karagila
and Schilhan, Lemma 9.3, restricted to finite sequences of nice names. -/
theorem groundRealDefinable_solovayInclusion_of_finite_transfer
    (htr : ∀ s n : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ i ∈ n, IsNiceName (booleanConditions (levyContext κ hG).P (levyContext κ hG).R)
        (levyContext κ hG).P ((ω : V) ×ˢ (ω : V)) (s ‘ i)) →
      (levyContext κ hG).OrbitTransfer groundFormula s n (solovayParam κ hG))
    (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  refine (levyContext κ hG).groundRealDefinable_booleanReal_of_finite_transfer groundFormula
    ?_ ?_ htr τ
  · rw [solovayParam_eq_check]
    exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · intro a
    exact (eval_groundFormula _ _).mpr (levy_isGround_check hAC hU hc hω hκ hG a)

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the transfer statement of Karagila and Schilhan, Lemma 9.3, for finite
sequences of nice names as its only open assumption. -/
theorem solovay_corollary_of_finite_transfer
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (htr : ∀ s n : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ i ∈ n, IsNiceName (booleanConditions (levyContext κ hG).P (levyContext κ hG).R)
        (levyContext κ hG).P ((ω : V) ×ˢ (ω : V)) (s ‘ i)) →
      (levyContext κ hG).OrbitTransfer groundFormula s n (solovayParam κ hG)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary_final hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion_of_finite_transfer hAC hU hc hω hκ hG htr)

end

end ZFVP
