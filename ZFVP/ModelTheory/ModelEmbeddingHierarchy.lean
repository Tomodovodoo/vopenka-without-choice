import ZFVP.ModelTheory.ModelEmbeddingRestriction
import ZFVP.ModelTheory.CriticalPoint

/-! Rank-segment action for elementary graphs between arbitrary ZF rank models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (δ : V) [IsOrdinal δ] [Nonempty (SetDomain (hierarchy δ))]
  [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankHierarchy_val (α : SetDomain (hierarchy δ)) (hα : IsOrdinal α) :
    (hierarchy α).val = hierarchy α.val := by
  let := hierarchy_transitive δ
  let := (ordinal_iff (hierarchy δ) α).mp hα
  have ha : α.val ∈ δ := by
    simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using α.property
  exact hierarchy_val (hierarchy δ) α hα
    ((hierarchy_transitive δ).transitive _ (hierarchy_mem ha))

theorem rankHierarchy_formula (r α : SetDomain (hierarchy δ)) :
    piOneHierarchyFormula.Evalb ![r, α] ↔ IsOrdinal α.val ∧ r.val = hierarchy α.val := by
  let := hierarchy_transitive δ
  change piOneHierarchyFormula.Evalb ![r, α] ↔ _
  rw [Defined.eval_iff]
  change (IsOrdinal α ∧ r = hierarchy α) ↔ _
  constructor
  · rintro ⟨ha, rfl⟩
    exact ⟨(ordinal_iff (hierarchy δ) α).mp ha, rankHierarchy_val δ α ha⟩
  · rintro ⟨ha, hr⟩
    have ha' := (ordinal_iff (hierarchy δ) α).mpr ha
    refine ⟨ha', Subtype.ext ?_⟩
    exact hr.trans (rankHierarchy_val δ α ha').symm

end TransitiveZF

theorem modelEmbedding_value_hierarchy {δ ε f α : V} [IsOrdinal δ] [IsOrdinal ε]
    [Nonempty (SetDomain (hierarchy δ))] [Nonempty (SetDomain (hierarchy ε))]
    [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain (hierarchy ε))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : IsOrdinal α) (hαδ : α ∈ hierarchy δ) :
    IsOrdinal (f ‘ α) ∧ f ‘ (hierarchy α) = hierarchy (f ‘ α) := by
  let := hα
  have ha : α ∈ δ := by simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using hαδ
  let a : SetDomain (hierarchy δ) := ⟨α, hαδ⟩
  let r : SetDomain (hierarchy δ) := ⟨hierarchy α, hierarchy_mem ha⟩
  have hs := (TransitiveZF.rankHierarchy_formula δ r a).mpr ⟨hα, rfl⟩
  have he := (h.eval_semisentence piOneHierarchyFormula ![r, a]).mp hs
  have hv : h.toFunction ∘ ![r, a] = ![h.toFunction r, h.toFunction a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  exact (TransitiveZF.rankHierarchy_formula ε (h.toFunction r) (h.toFunction a)).mp he

end ZFVP
