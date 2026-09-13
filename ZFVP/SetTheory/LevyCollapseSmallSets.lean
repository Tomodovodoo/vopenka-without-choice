import ZFVP.SetTheory.LevyCollapseChainCondition
import ZFVP.SetTheory.FiniteNaturalSets

/-! Small subsets of a regular cardinal are bounded, the subcollapses below `κ` are small, and
the Levy collapse makes every column total and surjective by density. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The union of the members of `S` with index `i`. -/
noncomputable def fiberUnion (S e i : V) : V := ⋃ˢ {s ∈ S ; e ‘ s = i}

theorem fiberUnion_definable_one (S e : V) : ℒₛₑₜ-function₁[V] (fiberUnion S e) := by
  have hd : ℒₛₑₜ-relation[V] (fun B i ↦ ∀ x, x ∈ B ↔ ∃ s, (s ∈ S ∧ e ‘ s = i) ∧ x ∈ s) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = fiberUnion S e (v 1) ↔ _
  rw [mem_ext_iff]
  constructor
  · intro h x
    rw [h x]
    unfold fiberUnion
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, mem_sep_iff.mp hs, hx⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, mem_sep_iff.mpr hs, hx⟩
  · intro h x
    rw [h x]
    unfold fiberUnion
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, mem_sep_iff.mpr hs, hx⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, mem_sep_iff.mp hs, hx⟩

/-- A subset of a regular cardinal of size below it is bounded. -/
theorem regular_small_subset_bounded {κ S μ : V} (hreg : IsRegularCardinal κ) (hS : S ⊆ κ)
    (hμ : μ ∈ κ) (hle : S ≤# μ) : ∃ ξ ∈ κ, S ⊆ ξ := by
  have := hreg.1.1
  obtain ⟨e, he, hinj⟩ := hle
  have := IsFunction.of_mem he
  have hde : domain e = S := domain_eq_of_mem_function he
  have hF := fiberUnion_definable_one S e
  have hsingle : ∀ s ∈ S, {s' ∈ S ; e ‘ s' = e ‘ s} = ({s} : V) := by
    intro s hs
    ext s'
    rw [mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨hs', he'⟩ := mem_sep_iff.mp h
      have h1 : ⟨s', e ‘ s'⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hs')
      have h2 : ⟨s, e ‘ s⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hs)
      rw [he'] at h1
      exact hinj s' s _ h1 h2
    · rintro rfl
      exact mem_sep_iff.mpr ⟨hs, rfl⟩
  let g := definableGraph μ _ hF
  have hval : ∀ s ∈ S, g ‘ (e ‘ s) = s := by
    intro s hs
    rw [value_definableGraph μ _ hF (function_value_mem he hs)]
    unfold fiberUnion
    rw [hsingle s hs, sUnion_singleton_eq]
  have hempty0 : (∅ : V) ∈ κ := hreg.2.1 _ empty_mem_ω
  have hg : g ∈ κ ^ μ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function μ _ hF)
    intro y hy
    obtain ⟨i, _, rfl⟩ := (repl_spec hF).mp hy
    by_cases hex : ∃ s ∈ S, e ‘ s = i
    · obtain ⟨s, hs, rfl⟩ := hex
      unfold fiberUnion
      rw [hsingle s hs, sUnion_singleton_eq]
      exact hS _ hs
    · have hempty : {s ∈ S ; e ‘ s = i} = ∅ := by
        ext s
        simp only [mem_sep_iff, not_mem_empty, iff_false, not_and]
        intro hs he'
        exact hex ⟨s, hs, he'⟩
      unfold fiberUnion
      rw [hempty, sUnion_empty_eq_empty]
      exact hempty0
  obtain ⟨ξ, hξ, hb⟩ := regularCardinal_maps_bounded hreg hμ hg
  refine ⟨ξ, hξ, fun s hs ↦ ?_⟩
  have := hb _ (function_value_mem he hs)
  rwa [hval s hs] at this

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- The subcollapse below an ordinal below `κ` has size below `κ`. -/
theorem levyCollapse_small {ξ : V} (hξ : ξ ∈ κ) : ∃ μ ∈ κ, levyCollapse ξ ≤# μ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  obtain ⟨γ₁, hγ₁, h1⟩ := regularCardinal_ordinal_prod_small hreg hξ hω
  have : IsOrdinal γ₁ := IsOrdinal.of_mem hγ₁
  obtain ⟨γ₂, hγ₂, h2⟩ := regularCardinal_ordinal_prod_small hreg hξ hγ₁
  obtain ⟨μ, hμ, h3⟩ := measurable_power_bounded hAC hU hc hγ₂
  refine ⟨μ, hμ, ?_⟩
  have hsub : levyCollapse ξ ⊆ ℘ (((ω : V) ×ˢ ξ) ×ˢ ξ) := fun p hp ↦
    mem_power_iff.mpr ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hp)).1
  exact (cardLE_of_subset hsub).trans
    ((power_cardLE_of_cardLE ((prod_cardLE_prod h1 (CardLE.refl _)).trans h2)).trans h3)

end

/-- The rows used by a condition in the column `β`. -/
noncomputable def columnRows (β p : V) : V := {n ∈ (ω : V) ; ∃ γ, ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ p}

theorem columnRows_finite {κ β p : V} (hp : p ∈ levyCollapse κ) : IsInternallyFinite (columnRows β p) := by
  apply internallyFinite_subset (internallyFinite_repl (fun z ↦ kpair.π₁ (kpair.π₁ z))
    (by definability) (levyCollapse_internallyFinite hp))
  intro n hn
  obtain ⟨_, γ, h⟩ := mem_sep_iff.mp hn
  exact (repl_spec _).mpr ⟨_, h, by simp⟩

/-- Adding a value in a fresh position keeps a condition. -/
theorem levyCollapse_insert {κ β p n γ : V} [IsOrdinal κ] (hp : p ∈ levyCollapse κ) (hn : n ∈ (ω : V))
    (hβ : β ∈ κ) (hγ : γ ∈ β) (hfresh : ∀ δ, ⟨⟨n, β⟩ₖ, δ⟩ₖ ∉ p) :
    insert ⟨⟨n, β⟩ₖ, γ⟩ₖ p ∈ levyCollapse κ := by
  have hfp := levyCollapse_finitePartialFunction hp
  refine (mem_levyCollapse_iff κ _).mpr ⟨?_, ?_⟩
  · apply finitePartialFunction_insert hfp (kpair_mem_iff.mpr ⟨hn, hβ⟩)
      (IsOrdinal.toIsTransitive.mem_trans hγ hβ)
    intro h
    obtain ⟨δ, hδ⟩ := mem_domain_iff.mp h
    exact hfresh δ hδ
  · intro m α δ h
    rcases mem_insert.mp h with h | h
    · obtain ⟨h1, rfl⟩ := kpair_iff.mp h
      obtain ⟨_, rfl⟩ := kpair_iff.mp h1
      exact hγ
    · exact levyCollapse_value hp h

/-- Every row of a nonempty column gets a value. -/
theorem levyColumn_total_dense {κ β n : V} [IsOrdinal κ] (hβ : β ∈ κ) (h0 : (∅ : V) ∈ β) (hn : n ∈ (ω : V)) :
    ForcingDense (levyCollapse κ) (levyOrder κ) {p ∈ levyCollapse κ ; ∃ γ, ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ p} := by
  refine ⟨sep_subset, fun p hp ↦ ?_⟩
  by_cases hex : ∃ γ, ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hex⟩, (levyCollapse_poset κ).1.2.1 p hp⟩
  · push Not at hex
    have hq := levyCollapse_insert hp hn hβ h0 hex
    exact ⟨_, mem_sep_iff.mpr ⟨hq, ∅, mem_insert.mpr (Or.inl rfl)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩

/-- Every value below `β` is taken in some row of the column `β`. -/
theorem levyColumn_value_dense {κ β γ : V} [IsOrdinal κ] (hβ : β ∈ κ) (hγ : γ ∈ β) :
    ForcingDense (levyCollapse κ) (levyOrder κ) {p ∈ levyCollapse κ ; ∃ n ∈ (ω : V), ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ p} := by
  refine ⟨sep_subset, fun p hp ↦ ?_⟩
  obtain ⟨n, hn, hnfresh⟩ := internallyFinite_fresh_natural (columnRows_finite (β := β) hp)
  have hfresh : ∀ δ, ⟨⟨n, β⟩ₖ, δ⟩ₖ ∉ p := fun δ h ↦ hnfresh (mem_sep_iff.mpr ⟨hn, δ, h⟩)
  have hq := levyCollapse_insert hp hn hβ hγ hfresh
  exact ⟨_, mem_sep_iff.mpr ⟨hq, n, hn, mem_insert.mpr (Or.inl rfl)⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩

end ZFVP
