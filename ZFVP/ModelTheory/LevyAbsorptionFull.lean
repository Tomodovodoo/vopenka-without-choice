import ZFVP.ModelTheory.LevyAbsorptionModel
import ZFVP.ModelTheory.SolovayFactorLemma
import ZFVP.SetTheory.LevyCollapseFull

/-! An extension by the upper collapse `Coll(ω, [β, κ))` is an extension by the full collapse
`Coll(ω, <κ)`: the small collapse `Coll(ω, <β)` is absorbed into a column above `β`, and the
product of the columns below and above `β` embeds densely into the full collapse. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An extension by `Coll(ω, [β, κ))` is an extension by `Coll(ω, <κ)`, compatibly with checks. -/
theorem exists_full_collapse_context (hAC : InternalChoice V) {κ β ν : V} [IsOrdinal κ] [IsOrdinal β]
    (hβ : β ∈ κ) (hω : (ω : V) ∈ κ) (hν : ν ∈ κ) (hsmall : levyCollapse β ≤# ν)
    (Z : ForcingContext V) (hZP : Z.P = levyCollapseAbove κ β)
    (hZR : Z.R = restrictedOrder (levyOrder κ) (levyCollapseAbove κ β)) :
    ∃ Z' : ForcingContext V, Z'.P = levyCollapse κ ∧ Z'.R = levyOrder κ ∧ Z'.one = ∅ ∧
      ∃ f : Z.Model ≃ Z'.Model, (∀ x y, f x ∈ f y ↔ x ∈ y) ∧ ∀ a : V, f (Z.check a) = Z'.check a := by
  have hβ' : β ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hβ
  have : IsOrdinal ν := IsOrdinal.of_mem hν
  have hβν : IsOrdinal (β ∪ ν) := ordinal_union_isOrdinal β ν
  have hlam0 : IsOrdinal ((β ∪ ν) ∪ (ω : V)) := ordinal_union_isOrdinal _ _
  have hlam : (β ∪ ν) ∪ (ω : V) ∈ κ := union_mem_of_ordinals (union_mem_of_ordinals hβ hν) hω
  have hβlam : β ⊆ (β ∪ ν) ∪ (ω : V) := fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))
  have hνlam : ν ⊆ (β ∪ ν) ∪ (ω : V) := fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))
  have hωlam : (ω : V) ⊆ (β ∪ ν) ∪ (ω : V) := subset_union_right _ _
  have hlamβ : (β ∪ ν) ∪ (ω : V) ∉ β := fun h ↦ mem_irrefl _ (hβlam _ h)
  have hlamC : (β ∪ ν) ∪ (ω : V) ∈ κ \ β := mem_sdiff_iff.mpr ⟨hlam, hlamβ⟩
  have hQ : levyCollapse β ≤# (β ∪ ν) ∪ (ω : V) := hsmall.trans (cardLE_of_subset hνlam)
  have hR : IsForcingPreorder (levyCollapse β) (levyOrder β) := (levyCollapse_poset β).1
  have htop : IsForcingTop (levyCollapse β) (levyOrder β) ∅ := levyCollapse_top β
  -- `Z` is an extension by the columns above `β`; pull back to the absorption poset
  obtain ⟨e₂, he₂⟩ := absorptionPoset_denseEmbedding_columns (κ := κ) hlam hlamC hωlam
  have he₂' : IsDenseEmbedding (absorptionPoset κ (κ \ β) ((β ∪ ν) ∪ (ω : V)))
      (absorptionOrder κ (κ \ β) ((β ∪ ν) ∪ (ω : V))) Z.P Z.R e₂ := by
    rw [hZP, hZR, upperOrder_eq_levyColumnsOrder, levyCollapseAbove_eq_levyColumns]
    exact he₂
  let A := Z.densePreimage (absorptionOrder_preorder κ (κ \ β) _) (absorptionPoset_top κ (κ \ β) _) he₂'
  -- push forward to the product `Coll(ω, <β) × Coll(columns above β)`
  obtain ⟨e₁, he₁⟩ := absorptionPoset_denseEmbedding_product (κ := κ) hlam hlamC hωlam hAC hR htop hQ
  have he₁' : IsDenseEmbedding A.P A.R (levyCollapse β ×ˢ levyColumns κ (κ \ β))
      (productOrder (levyCollapse β) (levyOrder β) (levyColumns κ (κ \ β)) (levyColumnsOrder κ (κ \ β))) e₁ :=
    he₁
  let X := A.denseImage (productOrder_preorder hR (levyColumnsOrder_preorder κ (κ \ β)))
    (product_top htop (levyColumns_top κ (κ \ β))) he₁'
  -- join the columns
  have hcols : levyColumns κ β = levyCollapse β := levyColumns_eq_levyCollapse hβ'
  have hcolsOrder : levyColumnsOrder κ β = levyOrder β := by
    unfold levyColumnsOrder
    rw [hcols]
    rfl
  have he₃ : IsDenseEmbedding X.P X.R (levyCollapse κ) (levyOrder κ) (columnJoin κ β) := by
    have h := columnJoin_denseEmbedding κ β
    unfold columnProduct columnProductOrder at h
    rw [hcols, hcolsOrder] at h
    exact h
  let Z' := X.denseImage (levyCollapse_poset κ).1 (levyCollapse_top κ) he₃
  refine ⟨Z', rfl, rfl, rfl, ?_⟩
  let f₁ : Z.Model ≃ A.Model :=
    (Z.densePreimageEquiv (absorptionOrder_preorder κ (κ \ β) _) (absorptionPoset_top κ (κ \ β) _) he₂').symm
  let f₂ : A.Model ≃ X.Model := A.denseEquiv (productOrder_preorder hR (levyColumnsOrder_preorder κ (κ \ β)))
    (product_top htop (levyColumns_top κ (κ \ β))) he₁'
  let f₃ : X.Model ≃ Z'.Model := X.denseEquiv (levyCollapse_poset κ).1 (levyCollapse_top κ) he₃
  refine ⟨(f₁.trans f₂).trans f₃, ?_, ?_⟩
  · intro x y
    simp only [Equiv.trans_apply]
    rw [X.denseEquiv_mem_iff, A.denseEquiv_mem_iff]
    change (Z.densePreimageEquiv _ _ he₂').symm x ∈ (Z.densePreimageEquiv _ _ he₂').symm y ↔ x ∈ y
    rw [← Z.densePreimageEquiv_mem_iff (absorptionOrder_preorder κ (κ \ β) _) (absorptionPoset_top κ (κ \ β) _) he₂',
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · intro a
    simp only [Equiv.trans_apply]
    have h1 : f₁ (Z.check a) = A.check a := by
      change (Z.densePreimageEquiv _ _ he₂').symm (Z.check a) = A.check a
      rw [← Z.densePreimageEquiv_check (absorptionOrder_preorder κ (κ \ β) _) (absorptionPoset_top κ (κ \ β) _) he₂' a,
        Equiv.symm_apply_apply]
    rw [h1]
    have h2 : f₂ (A.check a) = X.check a := A.denseEquiv_check _ _ he₁' a
    rw [h2]
    exact X.denseEquiv_check _ _ he₃ a

end ZFVP
