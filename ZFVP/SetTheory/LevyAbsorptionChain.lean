import ZFVP.SetTheory.AbsorptionInfinite
import ZFVP.SetTheory.ProductEmbeddings
import ZFVP.SetTheory.LevyColumnSplittingRelative
import ZFVP.SetTheory.LevySingleColumn

/-! The poset-level absorption chain: for a poset `Q` of size at most an infinite column `λ ∈ C'`,
the poset `Y := λ^{<ω} × Coll(columns C' \ {λ})` embeds densely both into `Q × Coll(columns C')`
and into `Coll(columns C')`. Hence any extension by `Q × Coll(columns C')` is an extension by
`Coll(columns C')`, after pulling the generic back to `Y` and pushing it forward. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The intermediate poset `λ^{<ω} × Coll(columns C' \ {λ})`. -/
noncomputable def absorptionPoset (κ C' lam : V) : V :=
  finiteSequences lam ×ˢ levyColumns κ (C' \ ({lam} : V))

noncomputable def absorptionOrder (κ C' lam : V) : V :=
  productOrder (finiteSequences lam) (sequenceOrder lam) (levyColumns κ (C' \ ({lam} : V)))
    (levyColumnsOrder κ (C' \ ({lam} : V)))

theorem levyColumnsOrder_preorder (κ C : V) : IsForcingPreorder (levyColumns κ C) (levyColumnsOrder κ C) :=
  (reverseInclusionOrder_poset _).1

theorem absorptionOrder_preorder (κ C' lam : V) :
    IsForcingPreorder (absorptionPoset κ C' lam) (absorptionOrder κ C' lam) :=
  productOrder_preorder (sequenceOrder_poset lam).1 (levyColumnsOrder_preorder _ _)

section

variable {κ C' lam : V} [IsOrdinal κ] (hlam : lam ∈ κ) (hlamC : lam ∈ C') (hω : (ω : V) ⊆ lam)

include hlam hlamC hω in
/-- `Y` embeds densely into `Coll(columns C')`. -/
theorem absorptionPoset_denseEmbedding_columns :
    ∃ e, IsDenseEmbedding (absorptionPoset κ C' lam) (absorptionOrder κ C' lam)
      (levyColumns κ C') (levyColumnsOrder κ C') e := by
  have hsub : ({lam} : V) ⊆ C' := by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    exact hlamC
  have e_a := sequence_collapse_denseEmbedding (lam := lam) (hω ∅ empty_mem_ω)
  have e_b := collapseToColumnMap_denseEmbedding (κ := κ) hlam
  have e_ab := e_a.comp (levyColumnsOrder_preorder κ ({lam} : V)) e_b
  have e_c := e_ab.productRight (levyColumnsOrder_preorder κ (C' \ ({lam} : V)))
  have e_d := columnJoinRel_denseEmbedding (κ := κ) hsub
  exact ⟨_, e_c.comp (levyColumnsOrder_preorder κ C') e_d⟩

include hlam hlamC hω in
/-- `Y` embeds densely into `Q × Coll(columns C')` when `|Q| ≤ λ`. -/
theorem absorptionPoset_denseEmbedding_product (hAC : InternalChoice V) {Q S one : V}
    (hR : IsForcingPreorder Q S) (htop : IsForcingTop Q S one) (hQ : Q ≤# lam) :
    ∃ e, IsDenseEmbedding (absorptionPoset κ C' lam) (absorptionOrder κ C' lam)
      (Q ×ˢ levyColumns κ C') (productOrder Q S (levyColumns κ C') (levyColumnsOrder κ C')) e := by
  have : IsOrdinal lam := IsOrdinal.of_mem hlam
  have hsub : ({lam} : V) ⊆ C' := by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    exact hlamC
  obtain ⟨e₁, he₁⟩ := exists_collapseProduct_denseEmbedding_ordinal hAC hR htop hω hQ
  have e₂ := he₁.productRight (levyColumnsOrder_preorder κ (C' \ ({lam} : V)))
  have e₃ := productAssoc_denseEmbedding hR (collapse_poset lam).1 (levyColumnsOrder_preorder κ (C' \ ({lam} : V)))
  have e₄ := (collapseToColumnMap_denseEmbedding (κ := κ) hlam).productRight
    (levyColumnsOrder_preorder κ (C' \ ({lam} : V)))
  have e₅ := columnJoinRel_denseEmbedding (κ := κ) hsub
  have e₄₅ := e₄.comp (levyColumnsOrder_preorder κ C') e₅
  have e₆ := e₄₅.productLeft hR
  have e₂₃ := e₂.comp (productOrder_preorder hR (productOrder_preorder (collapse_poset lam).1
    (levyColumnsOrder_preorder κ (C' \ ({lam} : V))))) e₃
  exact ⟨_, e₂₃.comp (productOrder_preorder hR (levyColumnsOrder_preorder κ C')) e₆⟩

end

end ZFVP
