import ZFVP.ModelTheory.LimitRankEmbedding
import ZFVP.ModelTheory.EmbeddingOmegaFixation
import ZFVP.SetTheory.ChoicelessInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Fixation of a natural needs only membership of that natural in the source. -/
theorem IsCodedMembershipEmbedding.value_natural_of_mem {A B f n : V}
    [IsTransitive A] [IsTransitive B] (h : IsCodedMembershipEmbedding A B f)
    (hn : n ∈ (ω : V)) (hnA : n ∈ A) : f ‘ n = n := by
  have hall : ∀ n ∈ (ω : V), n ∈ A → f ‘ n = n := by
    apply naturalNumber_induction (fun n ↦ n ∈ A → f ‘ n = n) (by definability)
    · exact h.value_empty
    · intro i _ ih hs
      have hi := (inferInstance : IsTransitive A).mem_trans (mem_succ_self i) hs
      rw [h.value_succ hi hs, ih hi]
  exact hall n hn hnA

theorem IsCriticalPoint.omega_subset {A B f κ : V} [IsTransitive A] [IsTransitive B]
    (hκ : IsCriticalPoint A f κ) (h : IsCodedMembershipEmbedding A B f) : (ω : V) ⊆ κ := by
  let := hκ.ordinal
  rcases IsOrdinal.mem_trichotomy κ (ω : V) with hl | he | hg
  · exact False.elim (hκ.moved (h.value_natural_of_mem hl hκ.mem_domain))
  · exact he ▸ subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hg

/-- Rank induction below the critical point needs only successor closure of the
source height. The target may be any transitive set. -/
theorem limitRankEmbedding_fixed_below_criticalPoint {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) :
    ∀ x ∈ hierarchy κ, f ‘ x = x := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive κ
  have hκδ : κ ∈ δ := by
    simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using hκ.mem_domain
  have hinc : ∀ x ∈ hierarchy κ, x ∈ hierarchy δ :=
    fun _ hx ↦ (hierarchy_transitive δ).mem_trans hx (hierarchy_mem hκδ)
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

/-- A fixed ordinal below the image of the critical point lies below the
critical point. This is the cutoff comparison in the common-prefix argument. -/
theorem IsCriticalPoint.fixed_ordinal_below_image {A B f κ α : V}
    [IsTransitive A] [IsTransitive B] [IsOrdinal α]
    (hκ : IsCriticalPoint A f κ) (h : IsCodedMembershipEmbedding A B f)
    (hα : α ∈ A) (hfix : f ‘ α = α) (hbound : α ∈ f ‘ κ) : α ∈ κ := by
  exact (h.value_mem_iff hα hκ.mem_domain).mp (hfix.symm ▸ hbound)

theorem limitRankEmbedding_criticalPoint_no_cofinalMap {δ B f κ a g : V}
    [IsOrdinal δ] [IsTransitive B]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (ha : a ∈ hierarchy κ) :
    ¬IsCofinalMap κ a g := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  have hκδ : κ ∈ δ := by
    simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using hκ.mem_domain
  intro hg
  have haδ := (hierarchy_transitive δ).mem_trans ha (hierarchy_mem hκδ)
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

/-- The inaccessible critical point required by restricted lifting, without
correctness assumptions on either endpoint. -/
theorem limitRankEmbedding_criticalPoint_inaccessible {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hω : (ω : V) ∈ hierarchy δ) :
    IsChoicelessInaccessible κ := by
  let := hierarchy_transitive δ
  let := hκ.ordinal
  exact ⟨hκ.ordinal, hκ.omega_lt_of_omega_mem h hω, fun α hα _ ↦
    limitRankEmbedding_criticalPoint_no_cofinalMap hδ h hκ (hierarchy_mem hα)⟩

end ZFVP
