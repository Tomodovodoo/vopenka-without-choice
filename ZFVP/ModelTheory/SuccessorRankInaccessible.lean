import ZFVP.ModelTheory.SuccessorRankOrdinal
import ZFVP.ModelTheory.EmbeddingOmegaFixation
import ZFVP.SetTheory.ChoicelessInaccessible

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_criticalPoint_no_rank_cofinalMap {δ ε e κ X g : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hκ : IsCriticalPoint (hierarchy (succ δ)) e κ) (hκδ : κ ∈ δ)
    (hX : X ∈ hierarchy κ) : ¬IsCofinalMap κ X g := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  intro hg
  have hκV : κ ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hκδ
  have hXV : X ∈ hierarchy δ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hκδ) _ hX
  have hgV := (hierarchy_transitive δ).mem_trans hg.1
    (function_mem_hierarchy_limit hδ.successor_closed hXV hκV)
  have hinc : hierarchy δ ⊆ hierarchy (succ δ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hmap := h.value_cofinalMap (hinc g hgV) (hinc X hXV) hκ.mem_domain hg
  have hfix := successorRankEmbedding_fixed_below_criticalPoint hδ hε h hκ hκδ
  rw [hfix X hX] at hmap
  obtain ⟨i, hi, hle⟩ := hmap.2 κ (hκ.lt_value h)
  have hiκ := (hierarchy_transitive κ).mem_trans hi hX
  have hgi := function_value_mem hg.1 hi
  have hv := h.value_apply (hinc g hgV) (hinc X hXV) (IsFunction.of_mem hg.1)
    (domain_eq_of_mem_function hg.1) hi
  rw [hfix i hiκ, hκ.fixed_below hgi] at hv
  rw [hv] at hle
  exact mem_irrefl (g ‘ i) (hle _ hgi)

end ZFVP
