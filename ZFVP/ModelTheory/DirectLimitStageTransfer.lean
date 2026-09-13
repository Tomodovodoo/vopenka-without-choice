import ZFVP.ModelTheory.DirectLimitStagePreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def directStageCardinalFormula : SetTheorySemisentence 1 :=
  regularCardinalFormula.and dependentChoiceBelowFormula

@[irreducible] def directLimitStageTransferFormula : SetTheorySemisentence 11 :=
  f“θ P R π E U K t D S o.
    !choicelessInaccessibleFormula θ ∧ !splitForcingSystemFormula θ P π E ∧
    (∀ i ∈ θ, !forcingPreorderFormula (!value.dfn P i) (!value.dfn R i)) ∧
    (∀ i ∈ θ, !forcingTopFormula (!value.dfn P i) (!value.dfn R i) (!value.dfn t i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      !forcingSplitProjectionFormula (!value.dfn P i) (!value.dfn R i) (!value.dfn P j) (!value.dfn R j)
        (!value.dfn π (!kpair.dfn i j)) (!value.dfn E (!kpair.dfn i j))) ∧
    (∀ i ∈ θ, !value.dfn P i ⊆ U) ∧ (∀ i ∈ θ, !value.dfn P i ∈ !hierarchyFormula θ) ∧
    (∀ i ∈ θ, !value.dfn K i ∈ θ) ∧ (∀ β ∈ θ, ∃ i ∈ θ, β ∈ !value.dfn K i) ∧
    (∀ i ∈ θ, ∀ p ∈ !value.dfn P i,
      !(checkedUnaryForcingFormula dependentChoiceBelowFormula) (!value.dfn P i) (!value.dfn R i) (!value.dfn t i) p (!value.dfn K i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !allProjectionQuotientClosedBelowFormula
      (!value.dfn P i) (!value.dfn R i) (!value.dfn t i) (!value.dfn P j) (!value.dfn R j)
        (!value.dfn π (!kpair.dfn i j)) (!value.dfn K i)) ∧
    !forcingDirectLimitFormula D θ P π E U ∧ !forcingThreadOrderFormula S θ R D ∧ !forcingTopFormula D S o →
    ∀ p ∈ D, !(checkedUnaryForcingFormula directStageCardinalFormula) D S o p θ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance directStageCardinalFormula_defined : ℒₛₑₜ-predicate[V]
    (fun θ ↦ IsRegularCardinal θ ∧ ∀ α ∈ θ, InternalDependentChoiceAt α) via directStageCardinalFormula :=
  ⟨fun v ↦ by
    change regularCardinalFormula.Evalb v ∧ dependentChoiceBelowFormula.Evalb v ↔ _
    simp⟩

theorem directLimit_stage_forced_countable [Countable V]
    {θ P R π E U K t D S one : V} (hθ : IsChoicelessInaccessible θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hsmall : ∀ i ∈ θ, P ‘ i ∈ hierarchy θ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ θ) (hcof : ∀ β ∈ θ, ∃ i ∈ θ, β ∈ K ‘ i)
    (hDC : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i) dependentChoiceBelowFormula
      (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (K ‘ i))
    (hD : D = forcingDirectLimit θ P π E U) (hS : S = forcingThreadOrder θ R D)
    (hone : IsForcingTop D S one) :
    ∀ p ∈ D, p ∈ forcingFormula D S directStageCardinalFormula (standardTuple ![checkName one θ]) := by
  have hDS : IsForcingPreorder D S := by rw [hS, hD]; exact forcingDirectLimit_preorder hR
  apply (all_forces_checked_iff_all_generics hDS hone directStageCardinalFormula).mpr
  intro G hG
  let B : ForcingContext V := ⟨D, S, one, G, hDS, hone, hG⟩
  exact (Defined.eval_iff _).mpr (B.directLimit_stage_cardinal hθ h hR ht hsplit hU hsmall hK hcof hDC hc hD (hS.trans (congrArg _ hD)))

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_directLimitStageTransferFormula (v : Fin 11 → V) : directLimitStageTransferFormula.Evalb v ↔
    (IsChoicelessInaccessible (v 0) → IsSplitForcingSystem (v 0) (v 1) (v 3) (v 4) →
      (∀ i ∈ v 0, IsForcingPreorder ((v 1) ‘ i) ((v 2) ‘ i)) →
      (∀ i ∈ v 0, IsForcingTop ((v 1) ‘ i) ((v 2) ‘ i) ((v 7) ‘ i)) →
      (∀ i ∈ v 0, ∀ j ∈ v 0, i ⊆ j → IsForcingSplitProjection ((v 1) ‘ i) ((v 2) ‘ i)
        ((v 1) ‘ j) ((v 2) ‘ j) ((v 3) ‘ ⟨i, j⟩ₖ) ((v 4) ‘ ⟨i, j⟩ₖ)) →
      (∀ i ∈ v 0, (v 1) ‘ i ⊆ v 5) → (∀ i ∈ v 0, (v 1) ‘ i ∈ hierarchy (v 0)) →
      (∀ i ∈ v 0, (v 6) ‘ i ∈ v 0) → (∀ β ∈ v 0, ∃ i ∈ v 0, β ∈ (v 6) ‘ i) →
      (∀ i ∈ v 0, ∀ p ∈ (v 1) ‘ i, p ∈ forcingFormula ((v 1) ‘ i) ((v 2) ‘ i) dependentChoiceBelowFormula
        (standardTuple ![checkName ((v 7) ‘ i) ((v 6) ‘ i)])) →
      (∀ i ∈ v 0, ∀ j ∈ v 0, i ⊆ j → ForcesProjectionQuotientClosedBelow ((v 1) ‘ i) ((v 2) ‘ i)
        ((v 7) ‘ i) ((v 1) ‘ j) ((v 2) ‘ j) ((v 3) ‘ ⟨i, j⟩ₖ) ((v 6) ‘ i)) →
      v 8 = forcingDirectLimit (v 0) (v 1) (v 3) (v 4) (v 5) →
      v 9 = forcingThreadOrder (v 0) (v 2) (v 8) → IsForcingTop (v 8) (v 9) (v 10) →
      ∀ p ∈ v 8, p ∈ forcingFormula (v 8) (v 9) directStageCardinalFormula
        (standardTuple ![checkName (v 10) (v 0)])) := by
  simp [directLimitStageTransferFormula]
  simp [Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]

private theorem directLimitStageTransfer_valid (v : Fin 11 → V) : directLimitStageTransferFormula.Evalb v := by
  apply eval_of_countable_zf directLimitStageTransferFormula
  intro W _ _ _ _ w
  apply (eval_directLimitStageTransferFormula w).mpr
  intro hθ h hR ht hsplit hU hs hK hcof hDC hc hD hS ho
  exact directLimit_stage_forced_countable hθ h hR ht hsplit hU hs hK hcof hDC hc hD hS ho

theorem directLimit_stage_forced
    {θ P R π E U K t D S one : V} (hθ : IsChoicelessInaccessible θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hsmall : ∀ i ∈ θ, P ‘ i ∈ hierarchy θ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ θ) (hcof : ∀ β ∈ θ, ∃ i ∈ θ, β ∈ K ‘ i)
    (hDC : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i) dependentChoiceBelowFormula
      (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (K ‘ i))
    (hD : D = forcingDirectLimit θ P π E U) (hS : S = forcingThreadOrder θ R D)
    (hone : IsForcingTop D S one) :
    ∀ p ∈ D, p ∈ forcingFormula D S directStageCardinalFormula (standardTuple ![checkName one θ]) :=
  (eval_directLimitStageTransferFormula ![θ, P, R, π, E, U, K, t, D, S, one]).mp
    (directLimitStageTransfer_valid _) hθ h hR ht hsplit hU hsmall hK hcof hDC hc hD hS hone

end ZFVP
