import ZFVP.ModelTheory.LimitRankEmbedding

/-! The critical-point rank criterion for embeddings from limit rank segments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem criticalPoint_exists_of_moved_ordinal {A f α : V} (hα : IsOrdinal α)
    (ha : α ∈ A) (hm : f ‘ α ≠ α) : ∃! κ, IsCriticalPoint A f κ :=
  leastOrdinal_existsUnique _ (by definability) ⟨α, hα, ha, hm⟩

theorem limitRankEmbedding_fixed_below_criticalPoint {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : ∀ x ∈ hierarchy κ, f ‘ x = x := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive κ
  have hκδ : κ ∈ δ := by
    simpa only [rank_of_ordinal] using (mem_hierarchy_iff_rank_mem _ _).mp hκ.mem_domain
  have hinc : hierarchy κ ⊆ hierarchy δ :=
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hκδ)
  apply projectedRank_induction (hierarchy κ) id (by definability)
    (fun x ↦ f ‘ x = x) (by definability)
  intro x hx ih
  have hrκ := (mem_hierarchy_iff_rank_mem x κ).mp hx
  have hr : rank (f ‘ x) = rank x :=
    (limitRankEmbedding_value_rank hδ h (hinc x hx)).symm.trans (hκ.fixed_below hrκ)
  have hfx : f ‘ x ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, hr]
    exact hrκ
  apply mem_ext
  intro y
  constructor
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hfx
    have hiy := ih y hyκ (hr ▸ rank_mem hy)
    exact (h.value_mem_iff (hinc y hyκ) (hinc x hx)).mp (by simpa [hiy] using hy)
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hx
    have hiy := ih y hyκ (rank_mem hy)
    simpa [hiy] using (h.value_mem_iff (hinc y hyκ) (hinc x hx)).mpr hy

theorem limitRankEmbedding_criticalPoint_noLowRankCofinalMaps {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : NoLowRankCofinalMaps κ := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  intro a ha g hg
  have hκδ : κ ∈ δ := by
    simpa only [rank_of_ordinal] using (mem_hierarchy_iff_rank_mem _ _).mp hκ.mem_domain
  have haδ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hκδ) a ha
  have hgδ := (hierarchy_transitive δ).mem_trans hg.1
    (function_mem_hierarchy_limit hδ haδ hκ.mem_domain)
  have hmap := h.value_cofinalMap hgδ haδ hκ.mem_domain hg
  have hfa := limitRankEmbedding_fixed_below_criticalPoint hδ h hκ a ha
  rw [hfa] at hmap
  obtain ⟨i, hi, hle⟩ := hmap.2 κ (hκ.lt_value h)
  have hik := (hierarchy_transitive κ).mem_trans hi ha
  have hfi := limitRankEmbedding_fixed_below_criticalPoint hδ h hκ i hik
  have hgi := function_value_mem hg.1 hi
  have hv := h.value_apply hgδ haδ (IsFunction.of_mem hg.1)
    (domain_eq_of_mem_function hg.1) hi
  rw [hfi, hκ.fixed_below hgi] at hv
  rw [hv] at hle
  exact mem_irrefl (g ‘ i) (hle _ hgi)

theorem limitRankEmbedding_criticalPoint_rankCriterion {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hω : (ω : V) ∈ κ) :
    IsRankCriterionHeight κ := by
  let := hierarchy_transitive δ
  exact ⟨hκ.ordinal, hω, fun _ ha ↦ hκ.succ_closed h ha,
    limitRankEmbedding_criticalPoint_noLowRankCofinalMaps hδ h hκ⟩

end ZFVP
