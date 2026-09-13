import ZFVP.ModelTheory.ProjectionStagePreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def singularLimitStageFormula : SetTheorySemisentence 1 :=
  limitOfRegularCardinalsFormula.and dependentChoiceAtFormula

@[irreducible] def singularLimitStageTransferFormula : SetTheorySemisentence 11 :=
  f“g θ P R t K π E C S o. !IsOrdinal.dfn g ∧ !isω ⊆ g ∧
    (∀ a ∈ g, !succ.dfn a ∈ g) ∧ !internalCofinalityFormula g ∈ g ∧
    (∀ i ∈ θ, !value.dfn K i ∈ g) ∧ (∀ a ∈ g, ∃ i ∈ θ, a ∈ !value.dfn K i) ∧
    (∀ i ∈ θ, !forcingPreorderFormula (!value.dfn P i) (!value.dfn R i)) ∧
    (∀ i ∈ θ, !forcingTopFormula (!value.dfn P i) (!value.dfn R i) (!value.dfn t i)) ∧
    (∀ i ∈ θ, !forcingSplitProjectionFormula (!value.dfn P i) (!value.dfn R i) C S
      (!value.dfn π i) (!value.dfn E i)) ∧
    (∀ i ∈ θ, ∀ p ∈ !value.dfn P i, !(checkedUnaryForcingFormula woodinStageCardinalFormula)
      (!value.dfn P i) (!value.dfn R i) (!value.dfn t i) p (!value.dfn K i)) ∧
    (∀ i ∈ θ, !allProjectionQuotientClosedBelowFormula (!value.dfn P i) (!value.dfn R i)
      (!value.dfn t i) C S (!value.dfn π i) (!value.dfn K i)) ∧
    !forcingPreorderFormula C S ∧ !forcingTopFormula C S o →
      ∀ p ∈ C, !(checkedUnaryForcingFormula singularLimitStageFormula) C S o p g”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance singularLimitStageFormula_defined : ℒₛₑₜ-predicate[V]
    (fun γ ↦ IsLimitOfRegularCardinals γ ∧ InternalDependentChoiceAt γ) via singularLimitStageFormula :=
  ⟨fun v ↦ by
    change limitOfRegularCardinalsFormula.Evalb v ∧ dependentChoiceAtFormula.Evalb v ↔ _
    simp⟩

theorem singularLimit_stage_forced_countable [Countable V] {γ θ P R t K π E C S one : V} [IsOrdinal γ]
    (hω : (ω : V) ⊆ γ) (hsucc : ∀ α ∈ γ, succ α ∈ γ) (hcf : internalCofinality γ ∈ γ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ γ) (hcof : ∀ α ∈ γ, ∃ i ∈ θ, α ∈ K ‘ i)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hπ : ∀ i ∈ θ, IsForcingSplitProjection (P ‘ i) (R ‘ i) C S (π ‘ i) (E ‘ i))
    (hs : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i)
      woodinStageCardinalFormula (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) C S (π ‘ i) (K ‘ i))
    (hCS : IsForcingPreorder C S) (hone : IsForcingTop C S one) :
    ∀ p ∈ C, p ∈ forcingFormula C S singularLimitStageFormula (standardTuple ![checkName one γ]) := by
  apply (all_forces_checked_iff_all_generics hCS hone singularLimitStageFormula).mpr
  intro G hG
  let B : ForcingContext V := ⟨C, S, one, G, hCS, hone, hG⟩
  exact (Defined.eval_iff _).mpr (B.projected_singular_limit_stage hω hsucc hcf hK hcof hR ht hπ hs hc)

private theorem forall_six_eq {T : Type*} (a b c d e f : T) (F : T → T → T → T → T → T → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_singularLimitStageTransferFormula (v : Fin 11 → V) :
    singularLimitStageTransferFormula.Evalb v ↔
      (IsOrdinal (v 0) → (ω : V) ⊆ v 0 → (∀ α ∈ v 0, succ α ∈ v 0) →
        internalCofinality (v 0) ∈ v 0 → (∀ i ∈ v 1, (v 5) ‘ i ∈ v 0) →
        (∀ α ∈ v 0, ∃ i ∈ v 1, α ∈ (v 5) ‘ i) →
        (∀ i ∈ v 1, IsForcingPreorder ((v 2) ‘ i) ((v 3) ‘ i)) →
        (∀ i ∈ v 1, IsForcingTop ((v 2) ‘ i) ((v 3) ‘ i) ((v 4) ‘ i)) →
        (∀ i ∈ v 1, IsForcingSplitProjection ((v 2) ‘ i) ((v 3) ‘ i) (v 8) (v 9) ((v 6) ‘ i) ((v 7) ‘ i)) →
        (∀ i ∈ v 1, ∀ p ∈ (v 2) ‘ i, p ∈ forcingFormula ((v 2) ‘ i) ((v 3) ‘ i)
          woodinStageCardinalFormula (standardTuple ![checkName ((v 4) ‘ i) ((v 5) ‘ i)])) →
        (∀ i ∈ v 1, ForcesProjectionQuotientClosedBelow ((v 2) ‘ i) ((v 3) ‘ i) ((v 4) ‘ i)
          (v 8) (v 9) ((v 6) ‘ i) ((v 5) ‘ i)) →
        IsForcingPreorder (v 8) (v 9) → IsForcingTop (v 8) (v 9) (v 10) →
        ∀ p ∈ v 8, p ∈ forcingFormula (v 8) (v 9) singularLimitStageFormula
          (standardTuple ![checkName (v 10) (v 0)])) := by
  simp [singularLimitStageTransferFormula]
  simp [Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]

private theorem singularLimitStageTransfer_valid (v : Fin 11 → V) :
    singularLimitStageTransferFormula.Evalb v := by
  apply eval_of_countable_zf singularLimitStageTransferFormula
  intro W _ _ _ _ w
  apply (eval_singularLimitStageTransferFormula w).mpr
  intro hγ hω hs hcf hK hcof hR ht hπ hstage hc hCS ho
  let := hγ
  exact singularLimit_stage_forced_countable hω hs hcf hK hcof hR ht hπ hstage hc hCS ho

theorem singularLimit_stage_forced {γ θ P R t K π E C S one : V} [IsOrdinal γ]
    (hω : (ω : V) ⊆ γ) (hsucc : ∀ α ∈ γ, succ α ∈ γ) (hcf : internalCofinality γ ∈ γ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ γ) (hcof : ∀ α ∈ γ, ∃ i ∈ θ, α ∈ K ‘ i)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hπ : ∀ i ∈ θ, IsForcingSplitProjection (P ‘ i) (R ‘ i) C S (π ‘ i) (E ‘ i))
    (hs : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i)
      woodinStageCardinalFormula (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) C S (π ‘ i) (K ‘ i))
    (hCS : IsForcingPreorder C S) (hone : IsForcingTop C S one) :
    ∀ p ∈ C, p ∈ forcingFormula C S singularLimitStageFormula (standardTuple ![checkName one γ]) :=
  (eval_singularLimitStageTransferFormula ![γ, θ, P, R, t, K, π, E, C, S, one]).mp
    (singularLimitStageTransfer_valid _) (show IsOrdinal γ from inferInstance)
      hω hsucc hcf hK hcof hR ht hπ hs hc hCS hone

end ZFVP
