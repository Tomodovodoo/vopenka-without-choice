import ZFVP.ModelTheory.SolovaySymmetricRange
import ZFVP.ModelTheory.LevyInternalLocalization

/-! The range of the Solovay symmetric inclusion is a definable class of the Levy extension.

`Set.range (solovaySymmetricInclusion hG)` is an external object: it quantifies over the
hereditarily symmetric names of `V`. With the ground model definable from one parameter
(`levy_isGround_iff`) it can be rewritten as an internal predicate of `V[G]`: `x` is in the range
exactly when some element `τ` of the ground is a hereditarily symmetric name for the Solovay
system and `x` is the value of `τ` at the Boolean generic set. The parameter carries five pieces:
the ground parameter, the checks of the poset, the group and the filter of the Solovay system, and
the Boolean generic set read inside the poset extension.

The symmetric names live over the Boolean completion, so the values are computed there. The
transport back to the poset extension is `booleanRealization`, the realization of the Boolean
extension inside the poset extension: it inverts `booleanEquiv`, so a value computed with the
Boolean generic set of `V[G]` is exactly the image of the corresponding element of the symmetric
model.

Being internal, the predicate can carry an ∈-induction inside `V[G]`. That is what
`solovay_range_induction` provides, and it is the tool the reverse hypothesis `hnm` of
`ZFVP.ModelTheory.SolovaySymmetricRange` needs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### Hereditary symmetry along an end extension -/

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Name stabilizers are preserved by an end extension. -/
theorem map_nameStabilizer (j : MembershipEndExtension V W) (Γ τ : V) :
    j (nameStabilizer Γ τ) = nameStabilizer (j Γ) (j τ) := by
  unfold nameStabilizer
  refine j.map_separation Γ (fun π ↦ nameAction π τ = τ) (fun π ↦ nameAction π (j τ) = j τ)
    (by definability) (by definability) ?_
  intro π _
  rw [← j.map_nameAction]
  exact ⟨fun h ↦ by rw [h], fun h ↦ j.injective h⟩

/-- Being a hereditarily symmetric name transfers both ways along an end extension. -/
theorem hereditarilySymmetricName_map_iff (j : MembershipEndExtension V W) (P Γ F τ : V) :
    IsHereditarilySymmetricName (j P) (j Γ) (j F) (j τ) ↔
      IsHereditarilySymmetricName P Γ F τ := by
  unfold IsHereditarilySymmetricName
  rw [j.forcingName_map_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h σ hσ
    have hj : j σ ∈ nameClosure (j τ) := by
      rw [← j.map_nameClosure]
      exact (j.mem_iff _ _).mpr hσ
    have := h (j σ) hj
    rw [← j.map_nameStabilizer] at this
    exact (j.mem_iff _ _).mp this
  · intro h σ' hσ'
    rw [← j.map_nameClosure] at hσ'
    obtain ⟨σ, hσ, rfl⟩ := j.endExtension _ σ' hσ'
    rw [← j.map_nameStabilizer, j.mem_iff]
    exact h σ hσ

end MembershipEndExtension

/-! ### The Boolean extension realized inside the poset extension -/

namespace ForcingContext

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (A : ForcingContext V)

/-- `booleanRealization` inverts `booleanEquiv`. Both are built from names by the same recursion,
so it is enough to check the two generators: checks and the generic set. -/
theorem booleanRealization_value_booleanEquiv (x : A.Model) :
    A.booleanRealization.value (A.booleanEquiv x) = x := by
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  have h1 : A.booleanEquiv (A.ofName τ) =
      nameValue A.recoveredRealization.genericSet
        (A.recoveredRealization.ground τ.val) :=
    A.recoveredRealization.value_ofName τ
  rw [h1]
  have h2 := A.booleanRealization.embedding.map_nameValue
    A.recoveredRealization.genericSet (A.recoveredRealization.ground τ.val)
  change A.booleanRealization.value
      (nameValue A.recoveredRealization.genericSet (A.recoveredRealization.ground τ.val)) =
    nameValue (A.booleanRealization.value A.recoveredRealization.genericSet)
      (A.booleanRealization.value (A.recoveredRealization.ground τ.val)) at h2
  rw [h2]
  have h3 : A.booleanRealization.value A.recoveredRealization.genericSet = A.genericSet :=
    A.booleanRealization_value_recovered
  have h4 : A.booleanRealization.value (A.recoveredRealization.ground τ.val) = A.check τ.val :=
    A.booleanRealization.value_check τ.val
  rw [h3, h4]
  exact A.nameValue_genericSet_check τ

theorem booleanEquiv_symm_eq_booleanRealization (y : A.booleanContext.Model) :
    A.booleanEquiv.symm y = A.booleanRealization.value y := by
  have h := A.booleanRealization_value_booleanEquiv (A.booleanEquiv.symm y)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### Values of symmetric names, read in the poset extension -/

/-- The image of the value of a hereditarily symmetric name is the value of the check of that
name at the Boolean generic set of the poset extension. -/
theorem niceInclusion_ofName (K : V) (τ : (A.niceSymmetricContext K).Name) :
    A.niceInclusion K ((A.niceSymmetricContext K).ofName τ) =
      nameValue A.booleanRealization.genericSet (A.check τ.val) := by
  have h0 : A.booleanEquiv (A.niceInclusion K ((A.niceSymmetricContext K).ofName τ)) =
      A.booleanContext.ofName ⟨τ.val, τ.property.1⟩ :=
    A.booleanEquiv_niceInclusion K _
  have h2 := congrArg A.booleanRealization.value h0
  rw [A.booleanRealization_value_booleanEquiv] at h2
  rw [h2, A.booleanRealization.value_ofName]
  rfl

/-- The range of the symmetric model inside the poset extension, described by ground names: `x`
is an image exactly when some hereditarily symmetric name of the ground has `x` as its value at
the Boolean generic set. -/
theorem mem_range_niceInclusion_iff (K : V) (x : A.Model) :
    x ∈ Set.range (A.niceInclusion K) ↔
      ∃ τ : V, IsHereditarilySymmetricName (A.niceSymmetricContext K).P
          (A.niceSymmetricContext K).Γ (A.niceSymmetricContext K).F τ ∧
        x = nameValue A.booleanRealization.genericSet (A.check τ) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := (A.niceSymmetricContext K).ofName_surjective y
    exact ⟨τ.val, τ.property, A.niceInclusion_ofName K τ⟩
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(A.niceSymmetricContext K).ofName ⟨τ, hτ⟩, ?_⟩
    exact A.niceInclusion_ofName K ⟨τ, hτ⟩

end ForcingContext

/-! ### The internal predicate -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `x` is in the range of the Solovay symmetric inclusion, read inside the extension. The
parameter is `r = ⟨g, ⟨P, ⟨Γ, ⟨F, Ġ⟩⟩⟩⟩`: `g` names the ground model, `P`, `Γ` and `F` are the
poset, the group and the filter of the symmetric system, and `Ġ` is the Boolean generic set. -/
def InSolovayRangeInternal (x r : M) : Prop :=
  ∃ τ : M, IsGround τ (kpair.π₁ r) ∧
    IsHereditarilySymmetricName (kpair.π₁ (kpair.π₂ r))
      (kpair.π₁ (kpair.π₂ (kpair.π₂ r)))
      (kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ r)))) τ ∧
    x = nameValue (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ r)))) τ

instance inSolovayRangeInternal_definable : ℒₛₑₜ-relation[M] InSolovayRangeInternal := by
  unfold InSolovayRangeInternal
  definability

end

/-! ### The parameter -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ : V} [IsOrdinal κ] {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The parameter of the internal range predicate: the ground parameter, the checks of the poset,
the group and the filter of the Solovay symmetric system, and the Boolean generic set. -/
noncomputable def solovayRangeParameter : (levyContext κ hG).Model :=
  ⟨levyGroundParameter κ hG,
    ⟨(levyContext κ hG).check (levySolovayContext κ hG).P,
      ⟨(levyContext κ hG).check (levySolovayContext κ hG).Γ,
        ⟨(levyContext κ hG).check (levySolovayContext κ hG).F,
          (levyContext κ hG).booleanRealization.genericSet⟩ₖ⟩ₖ⟩ₖ⟩ₖ

omit [IsOrdinal κ] in
theorem solovayRangeParameter_ground :
    kpair.π₁ (solovayRangeParameter hG) = levyGroundParameter κ hG := by
  unfold solovayRangeParameter
  rw [kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem solovayRangeParameter_P :
    kpair.π₁ (kpair.π₂ (solovayRangeParameter hG)) =
      (levyContext κ hG).check (levySolovayContext κ hG).P := by
  unfold solovayRangeParameter
  rw [kpair.π₂_kpair, kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem solovayRangeParameter_group :
    kpair.π₁ (kpair.π₂ (kpair.π₂ (solovayRangeParameter hG))) =
      (levyContext κ hG).check (levySolovayContext κ hG).Γ := by
  unfold solovayRangeParameter
  rw [kpair.π₂_kpair, kpair.π₂_kpair, kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem solovayRangeParameter_filter :
    kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ (solovayRangeParameter hG)))) =
      (levyContext κ hG).check (levySolovayContext κ hG).F := by
  unfold solovayRangeParameter
  rw [kpair.π₂_kpair, kpair.π₂_kpair, kpair.π₂_kpair, kpair.π₁_kpair]

omit [IsOrdinal κ] in
/-- The poset of the Solovay system is built from `κ` alone. -/
theorem levySolovayContext_P :
    (levySolovayContext κ hG).P = booleanConditions (levyCollapse κ) (levyOrder κ) := rfl

omit [IsOrdinal κ] in
/-- The group of the Solovay system is built from `κ` alone. -/
theorem levySolovayContext_group :
    (levySolovayContext κ hG).Γ =
      forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) := rfl

omit [IsOrdinal κ] in
/-- The filter of the Solovay system is built from `κ` and `ω`. -/
theorem levySolovayContext_filter :
    (levySolovayContext κ hG).F =
      niceNameFilter (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)))
        (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) := rfl

omit [IsOrdinal κ] in
theorem solovayRangeParameter_generic :
    kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (solovayRangeParameter hG)))) =
      (levyContext κ hG).booleanRealization.genericSet := by
  unfold solovayRangeParameter
  rw [kpair.π₂_kpair, kpair.π₂_kpair, kpair.π₂_kpair, kpair.π₂_kpair]

end

/-! ### The range is internally definable -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The range of the Solovay symmetric inclusion is the class of values at the Boolean generic
set of the ground elements that are hereditarily symmetric names for the Solovay system. -/
theorem solovay_range_iff_internal (x : (levyContext κ hG).Model) :
    x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) ↔
      InSolovayRangeInternal x (solovayRangeParameter hG) := by
  have hrange := (levyContext κ hG).mem_range_niceInclusion_iff ((ω : V) ×ˢ (ω : V)) x
  constructor
  · intro hx
    obtain ⟨τ, hτ, hval⟩ := hrange.mp hx
    refine ⟨(levyContext κ hG).check τ, ?_, ?_, ?_⟩
    · rw [solovayRangeParameter_ground]
      exact levy_isGround_check hAC hU hc hω hκ hG τ
    · rw [solovayRangeParameter_P, solovayRangeParameter_group, solovayRangeParameter_filter]
      exact ((levyContext κ hG).checkEmbedding.hereditarilySymmetricName_map_iff
        (levySolovayContext κ hG).P (levySolovayContext κ hG).Γ
        (levySolovayContext κ hG).F τ).mpr hτ
    · rw [solovayRangeParameter_generic]
      exact hval
  · rintro ⟨t, hgr, hsym, hval⟩
    rw [solovayRangeParameter_ground] at hgr
    obtain ⟨τ, rfl⟩ := levy_check_of_isGround hAC hU hc hω hκ hG hgr
    rw [solovayRangeParameter_P, solovayRangeParameter_group,
      solovayRangeParameter_filter] at hsym
    rw [solovayRangeParameter_generic] at hval
    refine hrange.mpr ⟨τ, ?_, hval⟩
    exact ((levyContext κ hG).checkEmbedding.hereditarilySymmetricName_map_iff
      (levySolovayContext κ hG).P (levySolovayContext κ hG).Γ
      (levySolovayContext κ hG).F τ).mp hsym

include hAC hU hc hω hκ in
/-- The range is a definable class of the Levy extension with one parameter. -/
theorem solovay_range_definable_class :
    ∃ (Q : (levyContext κ hG).Model → (levyContext κ hG).Model → Prop)
      (_ : ℒₛₑₜ-relation[(levyContext κ hG).Model] Q) (r : (levyContext κ hG).Model),
      ∀ x : (levyContext κ hG).Model,
        x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) ↔ Q x r :=
  ⟨InSolovayRangeInternal, inSolovayRangeInternal_definable, solovayRangeParameter hG,
    solovay_range_iff_internal hAC hU hc hω hκ hG⟩

include hAC hU hc hω hκ in
/-- ∈-induction restricted to the range. The range is transitive, so the induction hypothesis is
available at every member; definability of the range is what lets the induction run inside the
extension. -/
theorem solovay_range_induction (P : (levyContext κ hG).Model → Prop)
    (hP : ℒₛₑₜ-predicate[(levyContext κ hG).Model] P)
    (step : ∀ x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)),
      (∀ y ∈ x, P y) → P x) :
    ∀ x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)), P x := by
  have key : ∀ x : (levyContext κ hG).Model,
      InSolovayRangeInternal x (solovayRangeParameter hG) → P x := by
    refine set_induction
      (fun x ↦ InSolovayRangeInternal x (solovayRangeParameter hG) → P x) (by definability) ?_
    intro x ih hx
    have hxr : x ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
      (solovay_range_iff_internal hAC hU hc hω hκ hG x).mpr hx
    refine step x hxr fun y hy ↦ ?_
    have hyr : y ∈ Set.range (solovaySymmetricInclusion (κ := κ) (hG := hG)) :=
      (levyContext κ hG).solovay_range_transitive x hxr y hy
    exact ih y hy ((solovay_range_iff_internal hAC hU hc hω hκ hG y).mp hyr)
  intro x hx
  exact key x ((solovay_range_iff_internal hAC hU hc hω hκ hG x).mp hx)

end

end ZFVP
