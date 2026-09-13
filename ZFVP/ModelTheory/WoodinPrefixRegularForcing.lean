import ZFVP.ModelTheory.WoodinPrefixRegular
import ZFVP.ModelTheory.WoodinPrefixNameFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinPrefixAllForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 5 :=
  f“P R o κ δ. ∃ Q S t, !woodinPrefixPosetNameFormula Q P R o κ δ ∧
    !reverseInclusionOrderNameFormula S P R Q ∧ !forcedEmptyNameFormula t P R ∧
      ∀ p ∈ !twoStepConditionsFormula P R Q t,
        !(checkedUnaryForcingFormula φ) (!twoStepConditionsFormula P R Q t)
          (!twoStepOrderFormula P R Q S t) (!kpair.dfn o t) p δ”

@[irreducible] def woodinPrefixRegularPreservationFormula : SetTheorySemisentence 5 :=
  f“P R o κ δ. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula regularCardinalFormula) P R o p κ) ∧
    !woodinPrefixCutoffFormula P R o κ δ ∧ P ∈ !hierarchyFormula δ →
      !(woodinPrefixAllForcingFormula regularCardinalFormula) P R o κ δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forall_three_eq {α : Type*} (a b c : α) (F : α → α → α → Prop) :
    (∀ x y z, x = a → y = b → z = c → F x y z) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, by rintro h x y z rfl rfl rfl; exact h⟩

private theorem forall_four_eq {α : Type*} (a b c d : α) (F : α → α → α → α → Prop) :
    (∀ x y z u, x = a → y = b → z = c → u = d → F x y z u) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, by rintro h x y z u rfl rfl rfl rfl; exact h⟩

private theorem forall_five_eq {α : Type*} (a b c d e : α) (F : α → α → α → α → α → Prop) :
    (∀ x y z u v, x = a → y = b → z = c → u = d → v = e → F x y z u v) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl, by rintro h x y z u v rfl rfl rfl rfl rfl; exact h⟩

private theorem forall_six_eq {α : Type*} (a b c d e f : α) (F : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    by rintro h u v w x y z rfl rfl rfl rfl rfl rfl; exact h⟩

theorem eval_woodinPrefixAllForcingFormula (φ : SetTheorySemisentence 1) (v : Fin 5 → V) :
    (woodinPrefixAllForcingFormula φ).Evalb v ↔
      ∀ p ∈ twoStepConditions (v 0) (v 1) (woodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
          (forcedEmptyName (v 0) (v 1)),
        p ∈ forcingFormula
          (twoStepConditions (v 0) (v 1) (woodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
            (forcedEmptyName (v 0) (v 1)))
          (twoStepOrder (v 0) (v 1) (woodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
            (woodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) (forcedEmptyName (v 0) (v 1))) φ
          (standardTuple ![checkName ⟨v 2, forcedEmptyName (v 0) (v 1)⟩ₖ (v 4)]) := by
  simp [woodinPrefixAllForcingFormula, woodinPrefixOrderName, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ,
    forall_three_eq, forall_four_eq, forall_five_eq, forall_six_eq]

theorem eval_woodinPrefixRegularPreservationFormula (v : Fin 5 → V) :
    woodinPrefixRegularPreservationFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula
          (standardTuple ![checkName (v 2) (v 3)])) →
        IsWoodinPrefixCutoff (v 0) (v 1) (v 2) (v 3) (v 4) → v 0 ∈ hierarchy (v 4) →
        (woodinPrefixAllForcingFormula regularCardinalFormula).Evalb v) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i
  simp [woodinPrefixRegularPreservationFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_three_eq, forall_five_eq, hv]

theorem woodinPrefixSuccessor_forces_regular_countable [Countable V] {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hPδ : P ∈ hierarchy δ) :
    (woodinPrefixAllForcingFormula regularCardinalFormula).Evalb ![P, R, one, κ, δ] := by
  apply (eval_woodinPrefixAllForcingFormula _ _).mpr
  let h := woodinPrefix_iterand hR htop hκ hδ
  intro p hp
  apply forces_checkedUnary_of_all_generics (twoStep_preorder hR htop h)
    (twoStep_top hR htop h) hp regularCardinalFormula
  intro G hG _
  exact (Defined.eval_iff _).mpr (woodinPrefixSuccessor_regular hR htop hκ hδ hPδ hG)

theorem woodinPrefixRegularPreservation_countable [Countable V] (v : Fin 5 → V) :
    woodinPrefixRegularPreservationFormula.Evalb v := by
  apply (eval_woodinPrefixRegularPreservationFormula v).mpr
  intro ho ht hk hd hp
  apply (eval_woodinPrefixAllForcingFormula _ v).mpr
  exact (eval_woodinPrefixAllForcingFormula _ ![v 0, v 1, v 2, v 3, v 4]).mp
    (woodinPrefixSuccessor_forces_regular_countable ho ht hk hd hp)

theorem woodinPrefixRegularPreservation_valid (v : Fin 5 → V) :
    woodinPrefixRegularPreservationFormula.Evalb v :=
  eval_of_countable_zf woodinPrefixRegularPreservationFormula
    (fun _W _ _ _ _ w ↦ woodinPrefixRegularPreservation_countable w) v

theorem woodinPrefixSuccessor_forces_regular {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hPδ : P ∈ hierarchy δ) :
    ∀ p ∈ twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R),
      p ∈ forcingFormula
        (twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R))
        (twoStepOrder P R (woodinPrefixPosetName P R one κ δ) (woodinPrefixOrderName P R one κ δ)
          (forcedEmptyName P R)) regularCardinalFormula
        (standardTuple ![checkName ⟨one, forcedEmptyName P R⟩ₖ δ]) := by
  have hh := (eval_woodinPrefixRegularPreservationFormula ![P, R, one, κ, δ]).mp
    (woodinPrefixRegularPreservation_valid ![P, R, one, κ, δ]) hR htop hκ hδ hPδ
  exact (eval_woodinPrefixAllForcingFormula _ ![P, R, one, κ, δ]).mp hh

end ZFVP
