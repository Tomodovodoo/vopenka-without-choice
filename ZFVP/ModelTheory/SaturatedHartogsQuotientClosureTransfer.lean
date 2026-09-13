import ZFVP.ModelTheory.SaturatedHartogsQuotientClosure
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def saturatedHartogsQuotientClosureTransferFormula : SetTheorySemisentence 14 :=
  f“P R b T U o τ E κ δ π η C S.
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R b ∧
    !forcingSplitProjectionFormula P R T U τ E ∧ !forcingPreorderFormula T U ∧ !forcingTopFormula T U o ∧
    !choicelessInaccessibleFormula δ ∧ T ∈ !hierarchyFormula δ ∧ κ ∈ δ ∧
    (∀ p ∈ T, !(namedUnaryForcingFormula regularCardinalFormula) T U p (!hartogsNumberNameFormula T U (!checkNameFormula o κ))) ∧
    !twoStepConditionsFormula C T U (!saturatedHartogsPosetNameFormula T U o κ δ) (!isEmpty) ∧
    !twoStepOrderFormula S T U (!saturatedHartogsPosetNameFormula T U o κ δ)
      (!saturatedHartogsOrderNameFormula T U o κ δ) (!isEmpty) ∧
    !forcingProjectionFormula P R C S π ∧ (∀ q ∈ C, !value.dfn τ (!kpair.π₁.dfn q) = !value.dfn π q) ∧
    !IsOrdinal.dfn η ∧ η ⊆ κ ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula dependentChoiceBelowFormula) P R b p η) ∧
    !allProjectionQuotientClosedBelowFormula P R b T U τ η →
    !allProjectionQuotientClosedBelowFormula P R b C S π η”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedHartogs_quotient_closure_forced_countable [Countable V]
    {P R one T U o τ E κ δ π η C S : V} [IsOrdinal η]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingSplitProjection P R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![hartogsNumberName T U (checkName o κ)]))
    (hC : C = twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
    (hS : S = twoStepOrder T U (saturatedHartogsPosetName T U o κ δ)
      (saturatedHartogsOrderName T U o κ δ) ∅)
    (hπ : IsForcingProjection P R C S π) (he : ∀ q ∈ C, τ ‘ (kpair.π₁ q) = π ‘ q)
    (hηκ : η ⊆ κ)
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one η]))
    (hbase : ForcesProjectionQuotientClosedBelow P R one T U τ η) :
    ForcesProjectionQuotientClosedBelow P R one C S π η := by
  subst C S
  have h := saturatedHartogsCollapse_iterand hU ho hδ hκ
  apply projectionQuotient_closedBelow_forced_of_generics hR htop hπ (twoStep_preorder hU ho h)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hc := A.projectionQuotient_closedBelow_of_forced hτ.projection hU hbase
  obtain ⟨p, hp⟩ := hG.1.2.1
  have hd : ∀ γ ∈ A.check η, InternalDependentChoiceAt γ :=
    (Defined.eval_iff _).mp ((A.formula_truth dependentChoiceBelowFormula
      ![⟨checkName one η, checkName_isName htop.1 η⟩]).mpr ⟨p, hp, hDC p (hG.1.1 p hp)⟩)
  exact A.saturatedHartogs_quotient_comp_closedBelow_countable hτ hU ho hδ hT hκδ hκ hπ.maps
    (fun q hq ↦ by rw [twoStepProjection_value hq]; exact he q hq)
    ((A.checkEmbedding.subset_iff η κ).mpr hηκ) hd hc

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

theorem eval_saturatedHartogsQuotientClosureTransferFormula (v : Fin 14 → V) :
    saturatedHartogsQuotientClosureTransferFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingSplitProjection (v 0) (v 1) (v 3) (v 4) (v 6) (v 7) →
        IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
        IsChoicelessInaccessible (v 9) → v 3 ∈ hierarchy (v 9) → v 8 ∈ v 9 →
        (∀ p ∈ v 3, p ∈ forcingFormula (v 3) (v 4) regularCardinalFormula
          (standardTuple ![hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 8))])) →
        v 12 = twoStepConditions (v 3) (v 4) (saturatedHartogsPosetName (v 3) (v 4) (v 5) (v 8) (v 9)) ∅ →
        v 13 = twoStepOrder (v 3) (v 4) (saturatedHartogsPosetName (v 3) (v 4) (v 5) (v 8) (v 9))
          (saturatedHartogsOrderName (v 3) (v 4) (v 5) (v 8) (v 9)) ∅ →
        IsForcingProjection (v 0) (v 1) (v 12) (v 13) (v 10) →
        (∀ q ∈ v 12, (v 6) ‘ (kpair.π₁ q) = (v 10) ‘ q) → IsOrdinal (v 11) → v 11 ⊆ v 8 →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) dependentChoiceBelowFormula
          (standardTuple ![checkName (v 2) (v 11)])) →
        ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 3) (v 4) (v 6) (v 11) →
        ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 12) (v 13) (v 10) (v 11)) := by
  simp [saturatedHartogsQuotientClosureTransferFormula]
  simp [Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_five_eq, forall_six_eq]

private theorem saturatedHartogsQuotientClosureTransfer_valid (v : Fin 14 → V) :
    saturatedHartogsQuotientClosureTransferFormula.Evalb v := by
  apply eval_of_countable_zf saturatedHartogsQuotientClosureTransferFormula
  intro W _ _ _ _ w
  apply (eval_saturatedHartogsQuotientClosureTransferFormula w).mpr
  intro hR ht hτ hU ho hδ hT hκδ hκ hC hS hπ he hη hηκ hDC hbase
  let := hη
  exact saturatedHartogs_quotient_closure_forced_countable hR ht hτ hU ho hδ hT hκδ hκ hC hS hπ he hηκ hDC hbase

theorem saturatedHartogs_quotient_closure_forced
    {P R one T U o τ E κ δ π η C S : V} [IsOrdinal η]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingSplitProjection P R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![hartogsNumberName T U (checkName o κ)]))
    (hC : C = twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
    (hS : S = twoStepOrder T U (saturatedHartogsPosetName T U o κ δ)
      (saturatedHartogsOrderName T U o κ δ) ∅)
    (hπ : IsForcingProjection P R C S π) (he : ∀ q ∈ C, τ ‘ (kpair.π₁ q) = π ‘ q)
    (hηκ : η ⊆ κ)
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one η]))
    (hbase : ForcesProjectionQuotientClosedBelow P R one T U τ η) :
    ForcesProjectionQuotientClosedBelow P R one C S π η :=
  (eval_saturatedHartogsQuotientClosureTransferFormula ![P, R, one, T, U, o, τ, E, κ, δ, π, η, C, S]).mp
    (saturatedHartogsQuotientClosureTransfer_valid _) hR htop hτ hU ho hδ hT hκδ hκ hC hS hπ he
      (show IsOrdinal η from inferInstance) hηκ hDC hbase

end ZFVP
