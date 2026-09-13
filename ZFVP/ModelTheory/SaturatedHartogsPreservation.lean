import ZFVP.ModelTheory.SaturatedHartogsFormulas

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def saturatedHartogsAllForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 5 :=
  f“P R o κ δ. ∀ Q S C T, !saturatedHartogsPosetNameFormula Q P R o κ δ →
    !saturatedHartogsOrderNameFormula S P R o κ δ → !twoStepConditionsFormula C P R Q (!isEmpty) →
    !twoStepOrderFormula T P R Q S (!isEmpty) →
    ∀ p ∈ C, !(checkedUnaryForcingFormula φ) C T (!kpair.dfn o (!isEmpty)) p δ”

@[irreducible] def saturatedHartogsPreservationFormula : SetTheorySemisentence 5 :=
  f“P R o κ δ. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    (∀ p ∈ P, !(namedUnaryForcingFormula regularCardinalFormula) P R p (!hartogsNumberNameFormula P R (!checkNameFormula o κ))) ∧
    !woodinNamedPrefixCutoffFormula P R o κ (!hartogsNumberNameFormula P R (!checkNameFormula o κ)) δ ∧ P ∈ !hierarchyFormula δ →
      !(saturatedHartogsAllForcingFormula woodinStageCardinalFormula) P R o κ δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_four_eq {β : Type*} (a b c d : β) (F : β → β → β → β → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → F u v w x) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, fun h u v w x hu hv hw hx ↦ by subst u v w x; exact h⟩
private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_saturatedHartogsAllForcingFormula (φ : SetTheorySemisentence 1) (v : Fin 5 → V) :
    (saturatedHartogsAllForcingFormula φ).Evalb v ↔
      ∀ p ∈ twoStepConditions (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅,
        p ∈ forcingFormula
          (twoStepConditions (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅)
          (twoStepOrder (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
            (saturatedHartogsOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅) φ
          (standardTuple ![checkName ⟨v 2, ∅⟩ₖ (v 4)]) := by
  simp [saturatedHartogsAllForcingFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_five_eq, forall_six_eq]
  constructor
  · intro h
    exact h _ _ _ _ rfl rfl rfl rfl
  · rintro h Q S C T rfl rfl rfl rfl
    exact h

theorem eval_saturatedHartogsPreservationFormula (v : Fin 5 → V) : saturatedHartogsPreservationFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3))])) →
      IsWoodinNamedPrefixCutoff (v 0) (v 1) (v 2) (v 3) (hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3))) (v 4) → v 0 ∈ hierarchy (v 4) →
      (saturatedHartogsAllForcingFormula woodinStageCardinalFormula).Evalb v) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i
  simp [saturatedHartogsPreservationFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_three_eq, forall_four_eq, forall_five_eq, forall_six_eq, hv]

theorem saturatedHartogsSuccessor_forces_cardinal_countable [Countable V] {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![hartogsNumberName P R (checkName one κ)]))
    (hδ : IsWoodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ)) δ) (hP : P ∈ hierarchy δ) :
    (saturatedHartogsAllForcingFormula woodinStageCardinalFormula).Evalb ![P, R, one, κ, δ] := by
  apply (eval_saturatedHartogsAllForcingFormula _ _).mpr
  let h := saturatedHartogsCollapse_iterand hR htop hδ.2.1 hκ
  intro p hp
  apply forces_checkedUnary_of_all_generics (twoStep_preorder hR htop h) (twoStep_top hR htop h) hp woodinStageCardinalFormula
  intro G hG _hpG
  exact (Defined.eval_iff _).mpr (saturatedHartogsSuccessor_cardinal hR htop hκ hδ hP hG)

private theorem saturatedHartogsPreservation_valid (v : Fin 5 → V) : saturatedHartogsPreservationFormula.Evalb v := by
  apply eval_of_countable_zf saturatedHartogsPreservationFormula
  intro W _ _ _ _ w
  apply (eval_saturatedHartogsPreservationFormula w).mpr
  intro hR htop hκ hδ hP
  have hh := saturatedHartogsSuccessor_forces_cardinal_countable hR htop hκ hδ hP
  have hw : ![w 0, w 1, w 2, w 3, w 4] = w := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i
  rwa [hw] at hh

private theorem saturatedHartogsPreservation_transfer (v : Fin 5 → V)
    (hR : IsForcingPreorder (v 0) (v 1)) (htop : IsForcingTop (v 0) (v 1) (v 2))
    (hκ : ∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3))]))
    (hδ : IsWoodinNamedPrefixCutoff (v 0) (v 1) (v 2) (v 3) (hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3))) (v 4)) (hP : v 0 ∈ hierarchy (v 4)) :
    ∀ p ∈ twoStepConditions (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅,
      p ∈ forcingFormula
        (twoStepConditions (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅)
        (twoStepOrder (v 0) (v 1) (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
          (saturatedHartogsOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅) woodinStageCardinalFormula
        (standardTuple ![checkName ⟨v 2, ∅⟩ₖ (v 4)]) :=
  (eval_saturatedHartogsAllForcingFormula _ v).mp
    ((eval_saturatedHartogsPreservationFormula v).mp (saturatedHartogsPreservation_valid v) hR htop hκ hδ hP)

theorem saturatedHartogsSuccessor_forces_cardinal {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![hartogsNumberName P R (checkName one κ)]))
    (hδ : IsWoodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ)) δ) (hP : P ∈ hierarchy δ) :
    ∀ p ∈ twoStepConditions P R (saturatedHartogsPosetName P R one κ δ) ∅,
      p ∈ forcingFormula (twoStepConditions P R (saturatedHartogsPosetName P R one κ δ) ∅)
        (twoStepOrder P R (saturatedHartogsPosetName P R one κ δ) (saturatedHartogsOrderName P R one κ δ) ∅)
        woodinStageCardinalFormula (standardTuple ![checkName ⟨one, ∅⟩ₖ δ]) :=
  saturatedHartogsPreservation_transfer ![P, R, one, κ, δ] hR htop hκ hδ hP

end ZFVP


