import ZFVP.SetTheory.WoodinCollapse

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCardinalSmall.insert {κ A : V} (hκ : IsRegularCardinal κ)
    (hA : IsCardinalSmall κ A) (a : V) : IsCardinalSmall κ (insert a A) := by
  classical
  by_cases ha : a ∈ A
  · have he : Insert.insert a A = A := by ext x; simp only [mem_insert]; grind
    rwa [he]
  · obtain ⟨α, hα, hinj⟩ := hA
    exact ⟨succ α, regularCardinal_succ_closed hκ hα,
      by simpa only [succ] using cardLE_insert_fresh hinj ha (mem_irrefl α)⟩

theorem woodinCollapse_insert {κ δ p α η x : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hα : α ∈ κ) (hη : η ∈ δ)
    (hxδ : x ∈ hierarchy δ) (hxη : x ∈ hierarchy (ordinalAdd (1 : V) η))
    (hfresh : ⟨α, η⟩ₖ ∉ domain p) : insert ⟨⟨α, η⟩ₖ, x⟩ₖ p ∈ woodinCollapse κ δ := by
  obtain ⟨hsub, hfun, hsmall, hval⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hfun
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, IsFunction.insert p _ x hfresh, ?_, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hα, hη⟩, hxδ⟩
    · exact hsub _ hz
  · simpa only [domain_insert] using hsmall.insert hκ ⟨α, η⟩ₖ
  · intro β ξ y hy
    rcases mem_insert.mp hy with he | hy
    · have hh := kpair_iff.mp he
      have hp := kpair_iff.mp hh.1
      simpa only [hp.2, hh.2] using hxη
    · exact hval β ξ y hy

theorem woodinCollapse_fresh_row {κ δ p : V} (hκ : IsInitialOrdinal κ)
    (hp : p ∈ woodinCollapse κ δ) (η : V) : ∃ α ∈ κ, ⟨α, η⟩ₖ ∉ domain p := by
  classical
  by_contra h
  have hall : ∀ α ∈ κ, ⟨α, η⟩ₖ ∈ domain p := by simpa only [not_exists, not_and, not_not] using h
  let F : V → V := fun α ↦ ⟨α, η⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph κ F hF
  have hf : f ∈ (domain p) ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _ hall
  have hinj : Injective f := by
    intro α β z hα hβ
    have ha := ((pair_mem_definableGraph_iff _ F hF α z).mp hα).2
    have hb := ((pair_mem_definableGraph_iff _ F hF β z).mp hβ).2
    exact (kpair_iff.mp (ha.symm.trans hb)).1
  obtain ⟨ξ, hξ, hsmall⟩ := ((mem_woodinCollapse _ _ _).mp hp).2.2.1
  exact hκ.2 ξ hξ ((show κ ≤# domain p from ⟨f, hf, hinj⟩).trans hsmall)

theorem woodinCollapse_value_dense {κ δ η x : V} (hκ : IsRegularCardinal κ)
    (hη : η ∈ δ) (hxδ : x ∈ hierarchy δ) (hxη : x ∈ hierarchy (ordinalAdd (1 : V) η)) :
    ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      {p ∈ woodinCollapse κ δ ; ∃ α ∈ κ, ⟨⟨α, η⟩ₖ, x⟩ₖ ∈ p} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨α, hα, hfresh⟩ := woodinCollapse_fresh_row hκ.1 hp η
  have hq := woodinCollapse_insert hκ hp hα hη hxδ hxη hfresh
  refine ⟨insert ⟨⟨α, η⟩ₖ, x⟩ₖ p, mem_sep_iff.mpr ⟨hq, α, hα, by simp⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, ?_⟩⟩
  exact fun z hz ↦ mem_insert.mpr (Or.inr hz)

theorem woodinCollapse_coordinate_dense {κ δ α η : V} (hκ : IsRegularCardinal κ)
    [IsOrdinal δ] (hα : α ∈ κ) (hη : η ∈ δ) :
    ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      {p ∈ woodinCollapse κ δ ; ⟨α, η⟩ₖ ∈ domain p} := by
  classical
  let := IsOrdinal.of_mem hη
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  have hzδ : (∅ : V) ∈ hierarchy δ := (mem_hierarchy_iff_of_ordinal _ _).mpr ⟨η, hη, by simp⟩
  have hzη : (∅ : V) ∈ hierarchy (ordinalAdd (1 : V) η) :=
    (mem_hierarchy_iff_of_ordinal _ _).mpr
      ⟨∅, subset_ordinalAdd (1 : V) η (∅ : V) (by change (0 : V) ∈ 1; simp), by simp⟩
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases hc : ⟨α, η⟩ₖ ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hc⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, subset_refl _⟩⟩
  · have hq := woodinCollapse_insert hκ hp hα hη hzδ hzη hc
    refine ⟨insert ⟨⟨α, η⟩ₖ, (∅ : V)⟩ₖ p, mem_sep_iff.mpr ⟨hq, by simp⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, ?_⟩⟩
    exact fun z hz ↦ mem_insert.mpr (Or.inr hz)

end ZFVP
