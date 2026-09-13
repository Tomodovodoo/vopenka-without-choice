import ZFVP.SetTheory.LevyCollapseChainCondition
import ZFVP.SetTheory.MaximalAntichains

/-! Antichains of the Levy collapse at a measurable ordinal have size below `κ`, so their
supports are bounded below `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The least ordinal below `κ` bounding the support of a condition. -/
noncomputable def supportBound (κ : V) : V → V :=
  leastOrdinalOrZero (fun p δ ↦ δ ∈ κ ∧ ordinalSupport p ⊆ δ) (by definability)

instance supportBound_definable (κ : V) : ℒₛₑₜ-function₁[V] (supportBound κ) :=
  leastOrdinalOrZero_definable _ _

/-- The support bound of the condition with index `i`, or `∅` if there is none. -/
noncomputable def indexedBound (κ A e i : V) : V :=
  ⋃ˢ {δ ∈ κ ; ∃ p ∈ A, e ‘ p = i ∧ δ = supportBound κ p}

theorem indexedBound_definable_one (κ A e : V) : ℒₛₑₜ-function₁[V] (indexedBound κ A e) := by
  have hd : ℒₛₑₜ-relation[V] (fun B i ↦ ∀ x, x ∈ B ↔
    ∃ δ, (δ ∈ κ ∧ ∃ p ∈ A, e ‘ p = i ∧ δ = supportBound κ p) ∧ x ∈ δ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = indexedBound κ A e (v 1) ↔ _
  rw [mem_ext_iff]
  constructor
  · intro h x
    rw [h x]
    unfold indexedBound
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨δ, hδ, hx⟩
      exact ⟨δ, mem_sep_iff.mp hδ, hx⟩
    · rintro ⟨δ, hδ, hx⟩
      exact ⟨δ, mem_sep_iff.mpr hδ, hx⟩
  · intro h x
    rw [h x]
    unfold indexedBound
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨δ, hδ, hx⟩
      exact ⟨δ, mem_sep_iff.mpr hδ, hx⟩
    · rintro ⟨δ, hδ, hx⟩
      exact ⟨δ, mem_sep_iff.mp hδ, hx⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hU hc in
theorem supportBound_spec {p : V} (hp : p ∈ levyCollapse κ) :
    supportBound κ p ∈ κ ∧ ordinalSupport p ⊆ supportBound κ p := by
  obtain ⟨δ, hδ, hsub⟩ := hU.finite_bounded hc (ordinalSupport_finite hp) (ordinalSupport_subset hp)
  have : IsOrdinal δ := IsOrdinal.of_mem hδ
  exact (leastOrdinalOrZero_spec (fun p δ ↦ δ ∈ κ ∧ ordinalSupport p ⊆ δ) (by definability) p
    ⟨δ, inferInstance, hδ, hsub⟩).2.1

include hAC hU hc hω hκ in
/-- No antichain of the Levy collapse has size `κ`. -/
theorem levyAntichain_not_cardLE {A : V}
    (hA : IsForcingAntichain (levyCollapse κ) (levyOrder κ) A) : ¬κ ≤# A := by
  rintro ⟨f, hf, hinj⟩
  have hf' : f ∈ levyCollapse κ ^ κ := mem_function_of_mem_function_of_subset hf hA.1
  obtain ⟨α, hα, β, hβ, hne, hcomp⟩ := levyCollapse_chainCondition hAC hU hc hf' hω hκ hinj
  have := IsFunction.of_mem hf
  have hdf : domain f = κ := domain_eq_of_mem_function hf
  have hne' : f ‘ α ≠ f ‘ β := by
    intro h
    have h1 : ⟨α, f ‘ α⟩ₖ ∈ f := kpair_value_mem (by rw [hdf]; exact hα)
    have h2 : ⟨β, f ‘ β⟩ₖ ∈ f := kpair_value_mem (by rw [hdf]; exact hβ)
    rw [h] at h1
    exact hne (hinj α β _ h1 h2)
  exact hA.2 _ (function_value_mem hf hα) _ (function_value_mem hf hβ) hne' hcomp

include hAC hU hc hω hκ in
/-- The supports of the conditions in an antichain are bounded below `κ`. -/
theorem levyAntichain_supports_bounded {A : V}
    (hA : IsForcingAntichain (levyCollapse κ) (levyOrder κ) A) :
    ∃ ξ ∈ κ, ∀ p ∈ A, ordinalSupport p ⊆ ξ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hwo := wellOrderable_of_internalChoice hAC A
  have hμeq := wellOrderedCardinal_cardEQ hwo
  have hμ := wellOrderedCardinal_initial hwo
  have := hμ.1
  have hμκ : wellOrderedCardinal A ∈ κ := by
    rcases IsOrdinal.mem_trichotomy (α := wellOrderedCardinal A) (β := κ) with h | h | h
    · exact h
    · exact (levyAntichain_not_cardLE hAC hU hc hω hκ hA (h ▸ hμeq.le)).elim
    · exact (levyAntichain_not_cardLE hAC hU hc hω hκ hA
        ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ h)).trans hμeq.le)).elim
  obtain ⟨e, he, hinj⟩ := hμeq.ge
  have := IsFunction.of_mem he
  have hde : domain e = A := domain_eq_of_mem_function he
  have hF := indexedBound_definable_one κ A e
  have hsingle : ∀ p ∈ A, {δ ∈ κ ; ∃ p' ∈ A, e ‘ p' = e ‘ p ∧ δ = supportBound κ p'} =
      ({supportBound κ p} : V) := by
    intro p hp
    ext δ
    rw [mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨_, p', hp', hep, rfl⟩ := mem_sep_iff.mp h
      have h1 : ⟨p', e ‘ p'⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hp')
      have h2 : ⟨p, e ‘ p⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hp)
      rw [hep] at h1
      rw [hinj p' p _ h1 h2]
    · rintro rfl
      exact mem_sep_iff.mpr ⟨(supportBound_spec hU hc (hA.1 _ hp)).1, p, hp, rfl, rfl⟩
  have hval : ∀ p ∈ A, indexedBound κ A e (e ‘ p) = supportBound κ p := by
    intro p hp
    unfold indexedBound
    rw [hsingle p hp, sUnion_singleton_eq]
  let g := definableGraph (wellOrderedCardinal A) _ hF
  have hempty0 : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans (IsOrdinal.empty_mem_iff_nonempty.mpr ω_nonempty) hω
  have hg : g ∈ κ ^ wellOrderedCardinal A := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ hF)
    intro y hy
    obtain ⟨i, _, rfl⟩ := (repl_spec hF).mp hy
    by_cases hex : ∃ p ∈ A, e ‘ p = i
    · obtain ⟨p, hp, rfl⟩ := hex
      rw [hval p hp]
      exact (supportBound_spec hU hc (hA.1 _ hp)).1
    · have hempty : {δ ∈ κ ; ∃ p ∈ A, e ‘ p = i ∧ δ = supportBound κ p} = ∅ := by
        ext δ
        simp only [mem_sep_iff, not_mem_empty, iff_false, not_and, not_exists]
        intro _ p hp hep _
        exact hex ⟨p, hp, hep⟩
      change ⋃ˢ {δ ∈ κ ; ∃ p ∈ A, e ‘ p = i ∧ δ = supportBound κ p} ∈ κ
      rw [hempty, sUnion_empty_eq_empty]
      exact hempty0
  obtain ⟨ξ, hξ, hbound⟩ := regularCardinal_maps_bounded hreg hμκ hg
  refine ⟨ξ, hξ, fun p hp ↦ ?_⟩
  have hb := hbound (e ‘ p) (function_value_mem he hp)
  rw [value_definableGraph _ _ hF (function_value_mem he hp), hval p hp] at hb
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  exact subset_trans (supportBound_spec hU hc (hA.1 _ hp)).2 (IsOrdinal.toIsTransitive.transitive _ hb)

end

end ZFVP
