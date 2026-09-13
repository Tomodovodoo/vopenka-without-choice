import ZFVP.ModelTheory.RankEmbeddingRestriction

/-! Rank and hierarchy action of coded embeddings between positive C(n) stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_value_rank {k l : ℕ} {δ ε f x : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f) (hx : x ∈ hierarchy δ) :
    f ‘ (rank x) = rank (f ‘ x) := by
  let a : SetDomain (hierarchy δ) := ⟨x, hx⟩
  let r : SetDomain (hierarchy δ) := ⟨rank x, hδ.rank_closed hx⟩
  have hs := (hδ.rank_formula_correct r a).mpr rfl
  have he := (h.eval_semisentence piOneRankFormula ![r, a]).mp hs
  have hv : h.toFunction ∘ ![r, a] = ![h.toFunction r, h.toFunction a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  have ht := hε.rank_formula_correct (h.toFunction r) (h.toFunction a)
  exact ht.mp he

theorem rankEmbedding_value_hierarchy {k l : ℕ} {δ ε f α : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : IsOrdinal α) (hαδ : α ∈ hierarchy δ) :
    IsOrdinal (f ‘ α) ∧ f ‘ (hierarchy α) = hierarchy (f ‘ α) := by
  let a : SetDomain (hierarchy δ) := ⟨α, hαδ⟩
  let r : SetDomain (hierarchy δ) := ⟨hierarchy α, hδ.hierarchy_closed hα hαδ⟩
  have hs := (hδ.hierarchy_formula_correct r a).mpr ⟨hα, rfl⟩
  have he := (h.eval_semisentence piOneHierarchyFormula ![r, a]).mp hs
  have hv : h.toFunction ∘ ![r, a] = ![h.toFunction r, h.toFunction a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  exact (hε.hierarchy_formula_correct (h.toFunction r) (h.toFunction a)).mp he

theorem rankEmbedding_value_ordinal {k l : ℕ} {δ ε f α : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : IsOrdinal α) (hαδ : α ∈ hierarchy δ) : IsOrdinal (f ‘ α) :=
  (rankEmbedding_value_hierarchy hδ hε h hα hαδ).1

theorem rankEmbedding_fixed_of_ordinal_fixed {k l : ℕ} {δ ε f : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hord : ∀ α ∈ hierarchy δ, IsOrdinal α → f ‘ α = α) :
    ∀ x ∈ hierarchy δ, f ‘ x = x := by
  let := hδ.ordinal
  let := hε.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  apply projectedRank_induction (hierarchy δ) id (by definability) (fun x ↦ f ‘ x = x) (by definability)
  intro x hx ih
  have hr : rank (f ‘ x) = rank x :=
    (rankEmbedding_value_rank hδ hε h hx).symm.trans (hord _ (hδ.rank_closed hx) inferInstance)
  have hfx : f ‘ x ∈ hierarchy δ := by
    rw [mem_hierarchy_iff_rank_mem, hr]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hx
  apply mem_ext
  intro y
  constructor
  · intro hy
    have hyA := (inferInstance : IsTransitive (hierarchy δ)).mem_trans hy hfx
    have hyr : rank y ∈ rank x := hr ▸ rank_mem hy
    have hiy := ih y hyA hyr
    exact (h.value_mem_iff hyA hx).mp (by simpa [hiy] using hy)
  · intro hy
    have hyA := (inferInstance : IsTransitive (hierarchy δ)).mem_trans hy hx
    have hiy := ih y hyA (rank_mem hy)
    simpa [hiy] using (h.value_mem_iff hyA hx).mpr hy

theorem rankEmbedding_nontrivial_moves_ordinal {k l : ℕ} {δ ε f : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hne : ∃ x ∈ hierarchy δ, f ‘ x ≠ x) :
    ∃ α : V, IsOrdinal α ∧ α ∈ hierarchy δ ∧ f ‘ α ≠ α := by
  classical
  by_contra hc
  have hfix : ∀ α ∈ hierarchy δ, IsOrdinal α → f ‘ α = α := by
    intro α hα ha
    by_contra hne
    exact hc ⟨α, ha, hα, hne⟩
  obtain ⟨x, hx, hnx⟩ := hne
  exact hnx (rankEmbedding_fixed_of_ordinal_fixed hδ hε h hfix x hx)

end ZFVP
