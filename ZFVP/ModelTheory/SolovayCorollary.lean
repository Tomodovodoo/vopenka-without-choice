import ZFVP.ModelTheory.SolovayModel
import ZFVP.ModelTheory.SolovaySymmetricContext
import ZFVP.SetTheory.VopenkaIsomorphism

/-! The paper's Corollary `cor:Solovay`, assembled for `SolovayHOD`.

Every clause of the corollary except Vopěnka's Principle is already a theorem about
`SolovayHOD κ hG` in `ZFVP.ModelTheory.SolovayModel`. The Vopěnka clause comes from the symmetric
side: `levySolovayModel_vopenkaInstance` gives every instance of the scheme in the symmetric model
of the Solovay system `O(B, Ṙ)`, and the paper's Lemma `lem:Solovay-symmetric` says the symmetric
model is `Sol` itself.

That last identification is the one step not proved here. It is isolated as a single hypothesis
`hrange`: the comparison map `solovaySymmetricInclusion`, which sends an element of the symmetric
model to the same set read in the poset extension, has range exactly the `IsHOD` sets. Nothing
weaker is assumed and nothing is postulated: `hrange` is an ordinary hypothesis of the two exported
corollaries, so a later module can discharge it and the corollaries become unconditional.

Given `hrange` the comparison map is a bijection onto `SolovayHOD κ hG` that preserves and reflects
membership, and `vopenkaInstance_of_membershipIso` carries the scheme across. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Membership in the poset extension transfers along the inverse of the Boolean comparison. -/
theorem booleanEquiv_symm_mem_iff (A : ForcingContext V) (u v : A.booleanContext.Model) :
    A.booleanEquiv.symm u ∈ A.booleanEquiv.symm v ↔ u ∈ v := by
  have h := A.booleanEquiv_mem_iff (A.booleanEquiv.symm u) (A.booleanEquiv.symm v)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-! ### The comparison map -/

omit [IsOrdinal κ] in
/-- An element of the symmetric model of the Solovay system, read as a set of the Levy extension:
take the underlying name value in the Boolean extension, then transport back along the isomorphism
between the Boolean and the poset extension. -/
noncomputable def solovaySymmetricInclusion :
    (levySolovayContext κ hG).Model → (levyContext κ hG).Model :=
  fun x => (levyContext κ hG).booleanEquiv.symm ((levySolovayContext κ hG).toOrdinary x)

omit [IsOrdinal κ] in
theorem solovaySymmetricInclusion_injective :
    Function.Injective (solovaySymmetricInclusion (κ := κ) (hG := hG)) := fun _ _ h ↦
  (levySolovayContext κ hG).toOrdinary_injective
    ((levyContext κ hG).booleanEquiv.symm.injective h)

omit [IsOrdinal κ] in
theorem solovaySymmetricInclusion_mem_iff (x y : (levySolovayContext κ hG).Model) :
    solovaySymmetricInclusion hG x ∈ solovaySymmetricInclusion hG y ↔ x ∈ y :=
  (booleanEquiv_symm_mem_iff (levyContext κ hG) _ _).trans
    ((levySolovayContext κ hG).toOrdinary_mem_iff x y)

/-! ### Turning the range hypothesis into an isomorphism -/

omit [IsOrdinal κ] in
/-- Under the range hypothesis every image of the comparison map is an `IsHOD` set. -/
theorem solovaySymmetricInclusion_isHOD
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)})
    (x : (levySolovayContext κ hG).Model) :
    IsHOD solovayPf (solovaySymmetricInclusion hG x) (solovayParam κ hG) := by
  have hx : solovaySymmetricInclusion hG x ∈
      Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := Set.mem_range_self x
  rw [hrange] at hx
  exact hx

omit [IsOrdinal κ] in
/-- The comparison map as a map into the class model `Sol`. -/
noncomputable def solovaySymmetricToHOD
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)})
    (x : (levySolovayContext κ hG).Model) : SolovayHOD κ hG :=
  toHOD solovayPf (solovayParam κ hG) (solovaySymmetricInclusion_isHOD hG hrange x)

omit [IsOrdinal κ] in
theorem solovaySymmetricToHOD_val
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)})
    (x : (levySolovayContext κ hG).Model) :
    (solovaySymmetricToHOD hG hrange x).val = solovaySymmetricInclusion hG x := rfl

omit [IsOrdinal κ] in
theorem solovaySymmetricToHOD_bijective
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)}) :
    Function.Bijective (solovaySymmetricToHOD hG hrange) := by
  constructor
  · intro x y h
    exact solovaySymmetricInclusion_injective hG (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) := by
      rw [hrange]
      exact hod_val_isHOD solovayPf (solovayParam κ hG) y
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

omit [IsOrdinal κ] in
/-- Under the range hypothesis the symmetric model of the Solovay system and the class model `Sol`
are the same membership structure (the content of `lem:Solovay-symmetric`). -/
noncomputable def solovaySymmetricEquiv
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)}) :
    (levySolovayContext κ hG).Model ≃ SolovayHOD κ hG :=
  Equiv.ofBijective _ (solovaySymmetricToHOD_bijective hG hrange)

omit [IsOrdinal κ] in
theorem solovaySymmetricEquiv_mem_iff
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)})
    (x y : (levySolovayContext κ hG).Model) :
    solovaySymmetricEquiv hG hrange x ∈ solovaySymmetricEquiv hG hrange y ↔ x ∈ y :=
  solovaySymmetricInclusion_mem_iff hG x y

/-! ### Vopěnka's Principle in `Sol` -/

include hAC hU hc hω hκ in
/-- If the comparison map has the `IsHOD` sets as its range, then `Sol` satisfies every instance of
Vopěnka's Principle that the ground model satisfies. This is `lem:Solovay-symmetric` combined with
`thm:preservation`, in the form used by `cor:Solovay`. -/
theorem solovay_vopenkaInstance_of_range
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)})
    (φ : SetTheorySemisentence 2) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    VopenkaInstance (V := SolovayHOD κ hG) φ := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact vopenkaInstance_of_membershipIso (solovaySymmetricEquiv hG hrange)
    (solovaySymmetricEquiv_mem_iff hG hrange) φ
    (levySolovayModel_vopenkaInstance κ hG hVP φ)

/-! ### The corollary -/

include hAC hU hc hω hκ in
/-- `cor:Solovay` without the perfect set property, so without countability of the ground model.
`Sol` models `ZF`, every instance of Vopěnka's Principle, `DC`, `LM`, `BP`, the failure of `AC`,
`κ̌ = ω₁^Sol`, and `κ̌` carries a nonprincipal `κ̌`-complete ultrafilter. The only hypothesis beyond
the standing ones is `hrange`, the identification of the symmetric model with `Sol`. -/
theorem solovay_corollary_of_range
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)}) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact ⟨solovay_models_zf hAC hU hc hω hκ hG,
    fun φ ↦ solovay_vopenkaInstance_of_range hAC hU hc hω hκ hG hVP hrange φ,
    solovay_dependentChoice hAC hU hc hω hκ hG,
    solovay_lebesgueMeasurable hAC hU hc hω hκ hG,
    solovay_baireProperty hAC hU hc hω hκ hG,
    solovay_not_internalChoice hAC hU hc hω hκ hG,
    solovay_hartogsNumber_omega hAC hU hc hω hκ hG,
    (solovay_ultrafilter hAC hU hc hω hκ hG).1,
    (solovay_ultrafilter hAC hU hc hω hκ hG).2⟩

include hAC hU hc hω hκ in
/-- `cor:Solovay`: over an arbitrary ground model of `ZFC` with a measurable-style ultrafilter on
`κ`, the Solovay class `Sol = HOD_{V ∪ R}^{V[G]}` models
`ZF + VP + DC + LM + BP + PSP + ¬AC` and `ω₁^Sol = κ̌` carries a nonprincipal `κ̌`-complete
ultrafilter. Clauses are in the order of the paper's statement.

`hrange` is `lem:Solovay-symmetric`: the symmetric model of the Solovay system is exactly `Sol`.
It is the only part of the corollary left open here. -/
theorem solovay_corollary
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hrange : Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) =
      {y : (levyContext κ hG).Model | IsHOD solovayPf y (solovayParam κ hG)}) :
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
      (solovayUltrafilter hAC hU hc hω hκ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact ⟨solovay_models_zf hAC hU hc hω hκ hG,
    fun φ ↦ solovay_vopenkaInstance_of_range hAC hU hc hω hκ hG hVP hrange φ,
    solovay_dependentChoice hAC hU hc hω hκ hG,
    solovay_lebesgueMeasurable hAC hU hc hω hκ hG,
    solovay_baireProperty hAC hU hc hω hκ hG,
    solovay_perfectSetProperty hAC hU hc hω hκ hG,
    solovay_not_internalChoice hAC hU hc hω hκ hG,
    solovay_hartogsNumber_omega hAC hU hc hω hκ hG,
    (solovay_ultrafilter hAC hU hc hω hκ hG).1,
    (solovay_ultrafilter hAC hU hc hω hκ hG).2⟩

end

end ZFVP
