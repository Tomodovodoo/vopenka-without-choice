import ZFVP.ModelTheory.LevyODLocalized
import ZFVP.ModelTheory.LevyGroundDefinable
import ZFVP.SetTheory.NameClosureRecursion

/-! Localization as a definable class of the Levy extension.

`IsLocalized` is an external predicate: it quantifies over the names of `V`. With the ground
model now definable from one parameter (Laver's theorem, `levy_isGround_iff`), it can be
rewritten as an internal predicate of `V[G]`: `x` lies in `V[G_ξ]` exactly when some element
`τ` of the ground is a forcing name for `Coll(ω, <ξ)` and `x` is the value of `τ` at the part
of the generic set below `ξ`. The parameter carries the three pieces the formula needs: `κ̌`,
the ground parameter and the generic set.

Being internal, the predicate can be used in an ∈-induction inside `V[G]`. That closes the
gap left open in `LevyODLocalized`: a parameter tree is a set `S` closed under taking the two
components of its pairs, so rank induction over `S` shows every element of `S` is localized,
and in particular the tree itself is. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_nameClosureStep (j : MembershipEndExtension V W) (τ f : V) :
    j (nameClosureStep τ f) = nameClosureStep (j τ) (j f) := by
  simp only [nameClosureStep, j.map_insert, j.map_sUnion, j.map_range]

theorem map_nameClosureRecursion (j : MembershipEndExtension V W) {N f : V}
    (hf : IsSubnameRecursion N nameClosureStep f) :
    IsSubnameRecursion (j N) nameClosureStep (j f) := by
  have : IsFunction f := hf.1
  refine ⟨j.map_function f, ?_, ?_⟩
  · rw [← j.map_relationDomain, hf.2.1]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
    rw [← j.map_value_total, hf.2.2 τ hτ, j.map_nameClosureStep, j.map_restrict,
      j.map_relationDomain]

/-- Name closures are preserved by an end extension. -/
theorem map_nameClosure (j : MembershipEndExtension V W) (τ : V) :
    j (nameClosure τ) = nameClosure (j τ) := by
  rw [nameClosure_eq_subnameRecursion τ, nameClosure_eq_subnameRecursion (j τ)]
  let f := subnameRecursionTable (nameClosureStep : V → V → V) (by definability) τ
  have hf : IsSubnameRecursion (nameClosure τ) nameClosureStep f :=
    subnameRecursionTable_spec _ _ _
  have hg := j.map_nameClosureRecursion hf
  have hτ : j τ ∈ j (nameClosure τ) := (j.mem_iff _ _).mpr (mem_nameClosure_self τ)
  have he := subnameRecursion_coherent (j.map_subnameClosed (nameClosure_closed τ))
    (nameClosure_closed (j τ)) hg
    (subnameRecursionTable_spec (nameClosureStep : W → W → W) (by definability) (j τ))
    (j τ) hτ (mem_nameClosure_self (j τ))
  change j (f ‘ τ) = _
  rw [j.map_value_total]
  exact he

/-- Being a forcing name transfers both ways along an end extension. -/
theorem forcingName_map_iff (j : MembershipEndExtension V W) (P τ : V) :
    IsForcingName (j P) (j τ) ↔ IsForcingName P τ := by
  refine ⟨fun h σ hσ z hz ↦ ?_, fun h ↦ j.map_forcingName h⟩
  have hjσ : j σ ∈ nameClosure (j τ) := by
    rw [← j.map_nameClosure]
    exact (j.mem_iff _ _).mpr hσ
  obtain ⟨υ, p, hp, he⟩ := h (j σ) hjσ (j z) ((j.mem_iff _ _).mpr hz)
  have hmem : ⟨υ, p⟩ₖ ∈ j σ := he ▸ (j.mem_iff _ _).mpr hz
  obtain ⟨υ₀, p₀, hυp, rfl, rfl⟩ := (j.pair_mem_image_iff σ υ p).mp hmem
  exact ⟨υ₀, p₀, (j.mem_iff _ _).mp hp, j.injective (by rw [j.map_kpair]; exact he)⟩

end MembershipEndExtension

/-! ### The internal predicates -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The ground predicate as a definable relation. `GroundPredicate` registers only the
`Defined` instance, which leaves `definability` unfolding the whole predicate. -/
instance isGround_definable : ℒₛₑₜ-relation[M] IsGround := groundFormula_defined.to_definable

/-- `x` lies in the `ξ`-th bounded stage, read inside the extension. The parameter is a triple
`r = ⟨κ̌, ⟨g, Ǧ⟩⟩`: `g` names the ground model and `Ǧ` is the generic set. -/
def InLevySubmodelInternal (ξ x r : M) : Prop :=
  ∃ τ : M, IsGround τ (kpair.π₁ (kpair.π₂ r)) ∧ IsForcingName (levyCollapse ξ) τ ∧
    x = nameValue (kpair.π₂ (kpair.π₂ r) ∩ levyCollapse ξ) τ

instance inLevySubmodelInternal_definable : ℒₛₑₜ-relation₃[M] InLevySubmodelInternal := by
  unfold InLevySubmodelInternal
  definability

/-- `x` lies in some bounded stage, read inside the extension. -/
def IsLocalizedInternal (x r : M) : Prop :=
  ∃ ξ ∈ kpair.π₁ r, InLevySubmodelInternal ξ x r

instance isLocalizedInternal_definable : ℒₛₑₜ-relation[M] IsLocalizedInternal := by
  unfold IsLocalizedInternal
  definability

end

/-! ### The parameter -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ : V} [IsOrdinal κ] {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The parameter of the internal localization predicate: the check of `κ`, the parameter
naming the ground model, and the generic set. -/
noncomputable def levyInternalParameter : (levyContext κ hG).Model :=
  ⟨(levyContext κ hG).check κ, ⟨levyGroundParameter κ hG, (levyContext κ hG).genericSet⟩ₖ⟩ₖ

omit [IsOrdinal κ] in
theorem levyInternalParameter_fst :
    kpair.π₁ (levyInternalParameter hG) = (levyContext κ hG).check κ := by
  unfold levyInternalParameter
  rw [kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem levyInternalParameter_ground :
    kpair.π₁ (kpair.π₂ (levyInternalParameter hG)) = levyGroundParameter κ hG := by
  unfold levyInternalParameter
  rw [kpair.π₂_kpair, kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem levyInternalParameter_generic :
    kpair.π₂ (kpair.π₂ (levyInternalParameter hG)) = (levyContext κ hG).genericSet := by
  unfold levyInternalParameter
  rw [kpair.π₂_kpair, kpair.π₂_kpair]

end

/-! ### The bounded stages are internally definable -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The `ξ`-th bounded stage is the class of values at the cut generic set of the ground
elements that are names for the subcollapse. -/
theorem inLevySubmodel_iff_internal {ξ : V} [IsOrdinal ξ] (hξ : ξ ⊆ κ)
    (x : (levyContext κ hG).Model) :
    InLevySubmodel ξ hξ hG x ↔
      InLevySubmodelInternal ((levyContext κ hG).check ξ) x (levyInternalParameter hG) := by
  have hLC : (levyContext κ hG).check (levyCollapse ξ) =
      levyCollapse ((levyContext κ hG).check ξ) :=
    (levyContext κ hG).checkEmbedding.map_levyCollapse ξ
  constructor
  · intro hx
    obtain ⟨τ, rfl⟩ := (inLevySubmodel_iff ξ hξ hG x).mp hx
    have hn : IsForcingName ((levyContext κ hG).check (levyCollapse ξ))
        ((levyContext κ hG).check τ.val) :=
      (levyContext κ hG).checkEmbedding.map_forcingName τ.property
    refine ⟨(levyContext κ hG).check τ.val, ?_, ?_, ?_⟩
    · rw [levyInternalParameter_ground]
      exact levy_isGround_check hAC hU hc hω hκ hG τ.val
    · rw [← hLC]
      exact hn
    · rw [levyInternalParameter_generic, ← hLC, nameValue_inter_of_name hn,
        (levyContext κ hG).nameValue_genericSet_check
          ⟨τ.val, τ.property.mono (levyCollapse_mono hξ)⟩]
  · rintro ⟨τ, hgr, hname, hval⟩
    rw [levyInternalParameter_ground] at hgr
    obtain ⟨τ₀, rfl⟩ := levy_check_of_isGround hAC hU hc hω hκ hG hgr
    rw [← hLC] at hname
    have hname₀ : IsForcingName (levyCollapse ξ) τ₀ :=
      ((levyContext κ hG).checkEmbedding.forcingName_map_iff (levyCollapse ξ) τ₀).mp hname
    have hn : IsForcingName ((levyContext κ hG).check (levyCollapse ξ))
        ((levyContext κ hG).check τ₀) :=
      (levyContext κ hG).checkEmbedding.map_forcingName hname₀
    refine (inLevySubmodel_iff ξ hξ hG x).mpr
      ⟨(⟨τ₀, hname₀⟩ : ForcingName (levySubContext ξ hξ hG).P), ?_⟩
    rw [hval, levyInternalParameter_generic, ← hLC, nameValue_inter_of_name hn,
      (levyContext κ hG).nameValue_genericSet_check
        ⟨τ₀, hname₀.mono (levyCollapse_mono hξ)⟩]

include hAC hU hc hω hκ in
/-- Localization is a definable class of the extension with one parameter. -/
theorem isLocalized_iff_internal (x : (levyContext κ hG).Model) :
    IsLocalized hG x ↔ IsLocalizedInternal x (levyInternalParameter hG) := by
  constructor
  · rintro ⟨ξ, hξ, hx⟩
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    refine ⟨(levyContext κ hG).check ξ, ?_, ?_⟩
    · rw [levyInternalParameter_fst]
      exact ((levyContext κ hG).check_mem_iff ξ κ).mpr hξ
    · exact (inLevySubmodel_iff_internal hAC hU hc hω hκ hG _ x).mp hx
  · rintro ⟨ξ', hξ', hx⟩
    rw [levyInternalParameter_fst] at hξ'
    obtain ⟨ξ, hξ, rfl⟩ := ((levyContext κ hG).mem_check_iff κ ξ').mp hξ'
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact ⟨ξ, hξ, (inLevySubmodel_iff_internal hAC hU hc hω hκ hG _ x).mpr hx⟩

end

/-! ### Parameter trees -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) (p : (levyContext κ hG).Model)

include hAC hU hc hω hκ in
/-- A parameter tree over localized allowed parameters is localized. The induction runs inside
the extension, on the closure set of the tree, ordered by rank. -/
theorem isLocalized_parameterTree
    (hall : ∀ y : (levyContext κ hG).Model, IsAllowed Pf y p → IsLocalized hG y)
    {P : (levyContext κ hG).Model} (hP : IsParameterTree Pf P p) : IsLocalized hG P := by
  obtain ⟨S, hPS, hS⟩ := hP
  have key : ∀ y ∈ S, IsLocalizedInternal y (levyInternalParameter hG) := by
    refine projectedRank_induction S (fun x ↦ x) (by definability)
      (fun y ↦ IsLocalizedInternal y (levyInternalParameter hG)) (by definability) ?_
    intro y hy ih
    rcases hS y hy with hal | ⟨a, ha, b, hb, rfl⟩
    · exact (isLocalized_iff_internal hAC hU hc hω hκ hG y).mp (hall y hal)
    · have h1 := (isLocalized_iff_internal hAC hU hc hω hκ hG a).mpr
        (ih a ha (rank_kpair_left_lt a b))
      have h2 := (isLocalized_iff_internal hAC hU hc hω hκ hG b).mpr
        (ih b hb (rank_kpair_right_lt a b))
      exact (isLocalized_iff_internal hAC hU hc hω hκ hG _).mp (isLocalized_kpair hG h1 h2)
  exact (isLocalized_iff_internal hAC hU hc hω hκ hG P).mpr (key P hPS)

include hAC hU hc hω hκ in
/-- A set ordinal definable from a parameter class whose allowed parameters are localized is
defined by a single formula from three localized parameters. -/
theorem isLocalized_isOD_parameters_of_allowed
    (hall : ∀ y : (levyContext κ hG).Model, IsAllowed Pf y p → IsLocalized hG y)
    {x : (levyContext κ hG).Model} (hx : IsOD Pf x p) :
    ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → (levyContext κ hG).Model),
      (∀ i, IsLocalized hG (v i)) ∧ ∀ b, b ∈ x ↔ φ.Evalb (b :> v) := by
  obtain ⟨α, φ₀, P, hα, hcode, hP, -, rfl⟩ := hx
  exact exists_localized_parameters_of_decode hG hω hα hcode
    (isLocalized_parameterTree hAC hU hc hω hκ hG Pf p hall hP)

end

end ZFVP
