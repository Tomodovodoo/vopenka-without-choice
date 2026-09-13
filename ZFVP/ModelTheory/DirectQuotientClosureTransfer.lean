import ZFVP.ModelTheory.ForcingLimitFormulas
import ZFVP.ModelTheory.DirectLimitQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def directQuotientClosureTransferFormula : SetTheorySemisentence 12 :=
  f“θ P R π E U i o η D S ρ.
    !choicelessInaccessibleFormula θ ∧ !value.dfn P i ∈ !hierarchyFormula θ ∧
    !splitForcingSystemFormula θ P π E ∧
    (∀ j ∈ θ, !forcingPreorderFormula (!value.dfn P j) (!value.dfn R j)) ∧
    !forcingTopFormula (!value.dfn P i) (!value.dfn R i) o ∧
    (∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      !forcingSplitProjectionFormula (!value.dfn P j) (!value.dfn R j) (!value.dfn P k) (!value.dfn R k)
        (!value.dfn π (!kpair.dfn j k)) (!value.dfn E (!kpair.dfn j k))) ∧
    (∀ j ∈ θ, !value.dfn P j ⊆ U) ∧ i ∈ θ ∧ η ⊆ θ ∧
    !forcingDirectLimitFormula D θ P π E U ∧ !forcingThreadOrderFormula S θ R D ∧
    !forcingThreadCoordinateFormula ρ D i ∧
    (∀ k ∈ θ, i ⊆ k → !allProjectionQuotientClosedBelowFormula
      (!value.dfn P i) (!value.dfn R i) o (!value.dfn P k) (!value.dfn R k) (!value.dfn π (!kpair.dfn i k)) η) →
    !allProjectionQuotientClosedBelowFormula (!value.dfn P i) (!value.dfn R i) o D S ρ η”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem directQuotient_closedBelow_forced_countable [Countable V]
    {θ P R π E U i one η D S ρ : V}
    (hθ : IsChoicelessInaccessible θ) (hsmall : P ‘ i ∈ hierarchy θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ j ∈ θ, IsForcingPreorder (P ‘ j) (R ‘ j))
    (ht : IsForcingTop (P ‘ i) (R ‘ i) one)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k) (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U) (hi : i ∈ θ) (hη : η ⊆ θ)
    (hD : D = forcingDirectLimit θ P π E U) (hS : S = forcingThreadOrder θ R D)
    (hρ : ρ = forcingThreadCoordinate D i)
    (hc : ∀ k ∈ θ, i ⊆ k → ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) one (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ) η) :
    ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) one D S ρ η := by
  subst D S ρ
  let := hθ.1
  have hπ := forcingDirectLimit_splitProjection h hi hU hsplit
  apply projectionQuotient_closedBelow_forced_of_generics (hR i hi) ht hπ.projection (forcingDirectLimit_preorder hR)
  intro G hG
  let A : ForcingContext V := ⟨_, _, one, G, hR i hi, ht, hG⟩
  apply A.directLimit_quotient_separative_closedBelow_of_small hθ hsmall h hi rfl hU hsplit
    ((A.checkEmbedding.subset_iff η θ).mpr hη)
  intro k hk hik
  exact A.projectionQuotient_closedBelow_of_forced (hsplit i hi k hk hik).projection (hR k hk) (hc k hk hik)

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_directQuotientClosureTransferFormula (v : Fin 12 → V) :
    directQuotientClosureTransferFormula.Evalb v ↔
      (IsChoicelessInaccessible (v 0) → (v 1) ‘ (v 6) ∈ hierarchy (v 0) →
        IsSplitForcingSystem (v 0) (v 1) (v 3) (v 4) →
        (∀ j ∈ v 0, IsForcingPreorder ((v 1) ‘ j) ((v 2) ‘ j)) →
        IsForcingTop ((v 1) ‘ (v 6)) ((v 2) ‘ (v 6)) (v 7) →
        (∀ j ∈ v 0, ∀ k ∈ v 0, j ⊆ k →
          IsForcingSplitProjection ((v 1) ‘ j) ((v 2) ‘ j) ((v 1) ‘ k) ((v 2) ‘ k)
            ((v 3) ‘ ⟨j, k⟩ₖ) ((v 4) ‘ ⟨j, k⟩ₖ)) →
        (∀ j ∈ v 0, (v 1) ‘ j ⊆ v 5) → v 6 ∈ v 0 → v 8 ⊆ v 0 →
        v 9 = forcingDirectLimit (v 0) (v 1) (v 3) (v 4) (v 5) →
        v 10 = forcingThreadOrder (v 0) (v 2) (v 9) → v 11 = forcingThreadCoordinate (v 9) (v 6) →
        (∀ k ∈ v 0, v 6 ⊆ k → ForcesProjectionQuotientClosedBelow ((v 1) ‘ (v 6)) ((v 2) ‘ (v 6)) (v 7)
          ((v 1) ‘ k) ((v 2) ‘ k) ((v 3) ‘ ⟨v 6, k⟩ₖ) (v 8)) →
        ForcesProjectionQuotientClosedBelow ((v 1) ‘ (v 6)) ((v 2) ‘ (v 6)) (v 7) (v 9) (v 10) (v 11) (v 8)) := by
  simp [directQuotientClosureTransferFormula]
  simp [Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]

private theorem directQuotientClosureTransfer_valid (v : Fin 12 → V) :
    directQuotientClosureTransferFormula.Evalb v := by
  apply eval_of_countable_zf directQuotientClosureTransferFormula
  intro W _ _ _ _ w
  apply (eval_directQuotientClosureTransferFormula w).mpr
  intro hθ hs h hR ht hsplit hU hi hη hD hS hρ hc
  exact directQuotient_closedBelow_forced_countable hθ hs h hR ht hsplit hU hi hη hD hS hρ hc

theorem directQuotient_closedBelow_forced
    {θ P R π E U i one η D S ρ : V}
    (hθ : IsChoicelessInaccessible θ) (hsmall : P ‘ i ∈ hierarchy θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ j ∈ θ, IsForcingPreorder (P ‘ j) (R ‘ j))
    (ht : IsForcingTop (P ‘ i) (R ‘ i) one)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k) (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U) (hi : i ∈ θ) (hη : η ⊆ θ)
    (hD : D = forcingDirectLimit θ P π E U) (hS : S = forcingThreadOrder θ R D)
    (hρ : ρ = forcingThreadCoordinate D i)
    (hc : ∀ k ∈ θ, i ⊆ k → ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) one (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ) η) :
    ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) one D S ρ η :=
  (eval_directQuotientClosureTransferFormula ![θ, P, R, π, E, U, i, one, η, D, S, ρ]).mp
    (directQuotientClosureTransfer_valid _) hθ hsmall h hR ht hsplit hU hi hη hD hS hρ hc

end ZFVP
