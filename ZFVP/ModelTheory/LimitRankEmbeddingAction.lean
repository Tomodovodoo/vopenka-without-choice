import ZFVP.ModelTheory.LimitRankAbsoluteness

/-! Coded elementary embeddings between limit rank segments preserve hierarchy levels. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem limitRankEmbedding_value_hierarchy {δ ε f α : V} [IsOrdinal δ] [IsOrdinal ε]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hε : ∀ β ∈ ε, succ β ∈ ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : IsOrdinal α) (hαδ : α ∈ hierarchy δ) :
    IsOrdinal (f ‘ α) ∧ f ‘ (hierarchy α) = hierarchy (f ‘ α) := by
  let := hα
  have hαδ' : α ∈ δ := by
    simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using hαδ
  let a : SetDomain (hierarchy δ) := ⟨α, hαδ⟩
  let r : SetDomain (hierarchy δ) := ⟨hierarchy α, hierarchy_mem hαδ'⟩
  have hs := (piOneHierarchyFormula_absolute_limit hδ r a).mpr ⟨hα, rfl⟩
  have he := (h.eval_semisentence piOneHierarchyFormula ![r, a]).mp hs
  have hv : h.toFunction ∘ ![r, a] = ![h.toFunction r, h.toFunction a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  exact (piOneHierarchyFormula_absolute_limit hε (h.toFunction r) (h.toFunction a)).mp he

end ZFVP
