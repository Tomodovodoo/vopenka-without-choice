import ZFVP.SetTheory.LevyAbsorptionChain
import ZFVP.ModelTheory.DensePreimageGeneric

/-! Model-level absorption: an extension by `Q × Coll(columns C')`, with `|Q| ≤ λ ∈ C'` infinite,
is an extension by `Coll(columns C')` (pull the generic back to `λ^{<ω} × Coll(columns C' \ {λ})`
and push it forward), compatibly with membership and checks. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem levyCut_empty (C : V) : levyCut C (∅ : V) = ∅ := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    exact (not_mem_empty (levyCut_subset C ∅ z hz)).elim
  · intro hz
    exact (not_mem_empty hz).elim

theorem empty_mem_levyColumns (κ C : V) : (∅ : V) ∈ levyColumns κ C :=
  (mem_levyColumns_iff _ _ _).mpr ⟨empty_mem_levyCollapse κ, levyCut_empty C⟩

theorem levyColumns_top (κ C : V) : IsForcingTop (levyColumns κ C) (levyColumnsOrder κ C) ∅ :=
  ⟨empty_mem_levyColumns κ C, fun p hp ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_levyColumns κ C, fun z hz ↦ (not_mem_empty hz).elim⟩⟩

theorem absorptionPoset_top (κ C' lam : V) :
    IsForcingTop (absorptionPoset κ C' lam) (absorptionOrder κ C' lam) ⟨∅, ∅⟩ₖ :=
  product_top (sequence_top lam) (levyColumns_top κ _)

/-- Absorption at the level of extensions: an extension by `Q × Coll(columns C')` is an extension
by `Coll(columns C')`. -/
theorem exists_columns_context (hAC : InternalChoice V) {κ C' lam : V} [IsOrdinal κ] (hlam : lam ∈ κ)
    (hlamC : lam ∈ C') (hω : (ω : V) ⊆ lam) {Q S one : V} (hR : IsForcingPreorder Q S)
    (htop : IsForcingTop Q S one) (hQ : Q ≤# lam) (X : ForcingContext V)
    (hXP : X.P = Q ×ˢ levyColumns κ C')
    (hXR : X.R = productOrder Q S (levyColumns κ C') (levyColumnsOrder κ C')) :
    ∃ Z : ForcingContext V, Z.P = levyColumns κ C' ∧ Z.R = levyColumnsOrder κ C' ∧ Z.one = ∅ ∧
      ∃ f : X.Model ≃ Z.Model, (∀ x y, (f x ∈ f y ↔ x ∈ y)) ∧ ∀ a : V, f (X.check a) = Z.check a := by
  obtain ⟨e₁, he₁⟩ := absorptionPoset_denseEmbedding_product hlam hlamC hω hAC hR htop hQ
  have he₁' : IsDenseEmbedding (absorptionPoset κ C' lam) (absorptionOrder κ C' lam) X.P X.R e₁ := by
    rw [hXP, hXR]
    exact he₁
  obtain ⟨e₂, he₂⟩ := absorptionPoset_denseEmbedding_columns hlam hlamC hω
  let A := X.densePreimage (absorptionOrder_preorder κ C' lam) (absorptionPoset_top κ C' lam) he₁'
  have he₂' : IsDenseEmbedding A.P A.R (levyColumns κ C') (levyColumnsOrder κ C') e₂ := he₂
  let Z := A.denseImage (levyColumnsOrder_preorder κ C') (levyColumns_top κ C') he₂'
  refine ⟨Z, rfl, rfl, rfl, ?_⟩
  let f₁ : X.Model ≃ A.Model :=
    (X.densePreimageEquiv (absorptionOrder_preorder κ C' lam) (absorptionPoset_top κ C' lam) he₁').symm
  let f₂ : A.Model ≃ Z.Model := A.denseEquiv (levyColumnsOrder_preorder κ C') (levyColumns_top κ C') he₂'
  refine ⟨f₁.trans f₂, ?_, ?_⟩
  · intro x y
    simp only [Equiv.trans_apply]
    rw [A.denseEquiv_mem_iff]
    change (X.densePreimageEquiv _ _ he₁').symm x ∈ (X.densePreimageEquiv _ _ he₁').symm y ↔ x ∈ y
    rw [← X.densePreimageEquiv_mem_iff (absorptionOrder_preorder κ C' lam) (absorptionPoset_top κ C' lam) he₁',
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · intro a
    simp only [Equiv.trans_apply]
    have h1 : f₁ (X.check a) = A.check a := by
      change (X.densePreimageEquiv _ _ he₁').symm (X.check a) = A.check a
      rw [← X.densePreimageEquiv_check (absorptionOrder_preorder κ C' lam) (absorptionPoset_top κ C' lam) he₁' a,
        Equiv.symm_apply_apply]
    rw [h1]
    exact A.denseEquiv_check (levyColumnsOrder_preorder κ C') (levyColumns_top κ C') he₂' a

end ZFVP
