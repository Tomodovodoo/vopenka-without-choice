import ZFVP.ModelTheory.SuccessorRankEmbedding
import ZFVP.ModelTheory.CriticalPointCofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_value_rank {δ ε e x : V} (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hx : x ∈ hierarchy δ) : e ‘ (rank x) = rank (e ‘ x) := by
  have he := successorRankEmbedding_pi_iff hδ hε h piOneRankFormula_piOne ![rank x, x]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hδ.rank_closed hx, hx])
  have ht : piOneRankFormula.Evalb ![rank x, x] := (eval_piOneRankFormula _ _).mpr rfl
  simpa using he.mp ht

theorem successorRankEmbedding_fixed_below_criticalPoint {δ ε e κ : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hκ : IsCriticalPoint (hierarchy (succ δ)) e κ) (hκδ : κ ∈ δ) :
    ∀ x ∈ hierarchy κ, e ‘ x = x := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let := hierarchy_transitive κ
  have hinc : hierarchy κ ⊆ hierarchy δ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hκδ)
  have hinc' : hierarchy κ ⊆ hierarchy (succ δ) :=
    subset_trans hinc (hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)))
  apply projectedRank_induction (hierarchy κ) id (by definability) (fun x ↦ e ‘ x = x) (by definability)
  intro x hx ih
  have hrκ := (mem_hierarchy_iff_rank_mem x κ).mp hx
  have hr : rank (e ‘ x) = rank x :=
    (successorRankEmbedding_value_rank hδ hε h (hinc x hx)).symm.trans (hκ.fixed_below hrκ)
  have hfx : e ‘ x ∈ hierarchy κ := by rw [mem_hierarchy_iff_rank_mem, hr]; exact hrκ
  apply mem_ext
  intro y
  constructor
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hfx
    have hiy := ih y hyκ (hr ▸ rank_mem hy)
    exact (h.value_mem_iff (hinc' y hyκ) (hinc' x hx)).mp (by simpa [hiy] using hy)
  · intro hy
    have hyκ := (hierarchy_transitive κ).mem_trans hy hx
    have hiy := ih y hyκ (rank_mem hy)
    simpa [hiy] using (h.value_mem_iff (hinc' y hyκ) (hinc' x hx)).mpr hy

theorem successorRankEmbedding_criticalPoint_no_cofinalMap {δ ε e κ α g : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hκ : IsCriticalPoint (hierarchy (succ δ)) e κ) (hκδ : κ ∈ δ) (hα : α ∈ κ) :
    ¬IsCofinalMap κ α g := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let := IsOrdinal.of_mem hα
  intro hg
  have hκV : κ ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hκδ
  have hαV : α ∈ hierarchy δ := (hierarchy_transitive δ).mem_trans hα hκV
  have hgV := (hierarchy_transitive δ).mem_trans hg.1 (function_mem_hierarchy_limit hδ.successor_closed hαV hκV)
  have hinc : hierarchy δ ⊆ hierarchy (succ δ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hm := h.value_cofinalMap (hinc g hgV) (hinc α hαV) hκ.mem_domain hg
  rw [hκ.fixed_below hα] at hm
  obtain ⟨i, hi, hle⟩ := hm.2 κ (hκ.lt_value h)
  have hik := IsOrdinal.toIsTransitive.mem_trans hi hα
  have hgi := function_value_mem hg.1 hi
  have hv := h.value_apply (hinc g hgV) (hinc α hαV) (IsFunction.of_mem hg.1)
    (domain_eq_of_mem_function hg.1) hi
  rw [hκ.fixed_below hik, hκ.fixed_below hgi] at hv
  rw [hv] at hle
  exact mem_irrefl (g ‘ i) (hle _ hgi)

theorem successorRankEmbedding_criticalPoint_initial {δ ε e κ : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hκ : IsCriticalPoint (hierarchy (succ δ)) e κ) (hκδ : κ ∈ δ) : IsInitialOrdinal κ := by
  let := hκ.ordinal
  refine ⟨hκ.ordinal, fun α hα hinj ↦ ?_⟩
  obtain ⟨g, hg, hr⟩ := surjection_of_injection hinj ⟨α, hα⟩
  apply successorRankEmbedding_criticalPoint_no_cofinalMap hδ hε h hκ hκδ hα (g := g)
  refine ⟨hg, fun z hz ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_range_iff.mp (hr.symm ▸ hz)
  let := IsFunction.of_mem hg
  exact ⟨i, (mem_of_mem_functions hg hi).1, by rw [value_eq_of_kpair_mem hi]⟩

theorem successorRankEmbedding_criticalPoint_regular {δ ε e κ : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hκ : IsCriticalPoint (hierarchy (succ δ)) e κ) (hκδ : κ ∈ δ) (hω : (ω : V) ⊆ κ) :
    IsRegularCardinal κ := by
  let := hκ.ordinal
  refine ⟨successorRankEmbedding_criticalPoint_initial hδ hε h hκ hκδ, hω, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
  · exact he
  · obtain ⟨g, hg⟩ := cofinalMap_exists κ
    exact False.elim (successorRankEmbedding_criticalPoint_no_cofinalMap hδ hε h hκ hκδ hlt hg)

end ZFVP
