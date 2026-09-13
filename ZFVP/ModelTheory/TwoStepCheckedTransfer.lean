import ZFVP.ModelTheory.TwoStepCheckedForcing
import ZFVP.SetTheory.ForcingIterandFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem forall_eq_args3 {α : Type*} (x0 x1 x2 : α) (F : α → α → α → Prop) :
    (∀ (a0 a1 a2 : α), a0 = x0 → a1 = x1 → a2 = x2 → F a0 a1 a2) ↔ F x0 x1 x2 :=
  ⟨fun h ↦ h x0 x1 x2 rfl rfl rfl, fun h a0 a1 a2 h0 h1 h2 ↦ by subst a0 a1 a2; exact h⟩

private theorem forall_eq_args4 {α : Type*} (x0 x1 x2 x3 : α) (F : α → α → α → α → Prop) :
    (∀ (a0 a1 a2 a3 : α), a0 = x0 → a1 = x1 → a2 = x2 → a3 = x3 → F a0 a1 a2 a3) ↔ F x0 x1 x2 x3 :=
  ⟨fun h ↦ h x0 x1 x2 x3 rfl rfl rfl rfl, fun h a0 a1 a2 a3 h0 h1 h2 h3 ↦ by subst a0 a1 a2 a3; exact h⟩

private theorem forall_eq_args5 {α : Type*} (x0 x1 x2 x3 x4 : α) (F : α → α → α → α → α → Prop) :
    (∀ (a0 a1 a2 a3 a4 : α), a0 = x0 → a1 = x1 → a2 = x2 → a3 = x3 → a4 = x4 → F a0 a1 a2 a3 a4) ↔ F x0 x1 x2 x3 x4 :=
  ⟨fun h ↦ h x0 x1 x2 x3 x4 rfl rfl rfl rfl rfl, fun h a0 a1 a2 a3 a4 h0 h1 h2 h3 h4 ↦ by subst a0 a1 a2 a3 a4; exact h⟩

private theorem forall_eq_args6 {α : Type*} (x0 x1 x2 x3 x4 x5 : α) (F : α → α → α → α → α → α → Prop) :
    (∀ (a0 a1 a2 a3 a4 a5 : α), a0 = x0 → a1 = x1 → a2 = x2 → a3 = x3 → a4 = x4 → a5 = x5 → F a0 a1 a2 a3 a4 a5) ↔ F x0 x1 x2 x3 x4 x5 :=
  ⟨fun h ↦ h x0 x1 x2 x3 x4 x5 rfl rfl rfl rfl rfl rfl, fun h a0 a1 a2 a3 a4 a5 h0 h1 h2 h3 h4 h5 ↦ by subst a0 a1 a2 a3 a4 a5; exact h⟩

def twoStepCheckedTransferFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 9 :=
  f“P R o Q S t a C T.
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ !forcingIterandFormula P R Q S t ∧
      !twoStepConditionsFormula C P R Q t ∧ !twoStepOrderFormula T P R Q S t →
    ((∀ p ∈ P, !(forcingTruthFormula (allCheckedForcingFormula φ)) p P R
        (!quadrupleTupleFormula Q S t (!checkNameFormula o a))) ↔
      ∀ p ∈ C, !(checkedUnaryForcingFormula φ) C T (!kpair.dfn o t) p a)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_twoStepCheckedTransferFormula (φ : SetTheorySemisentence 1) (v : Fin 9 → V) :
    (twoStepCheckedTransferFormula φ).Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingIterand (v 0) (v 1) (v 3) (v 4) (v 5) →
        v 7 = twoStepConditions (v 0) (v 1) (v 3) (v 5) →
        v 8 = twoStepOrder (v 0) (v 1) (v 3) (v 4) (v 5) →
        ((∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) (allCheckedForcingFormula φ)
          (standardTuple ![v 3, v 4, v 5, checkName (v 2) (v 6)])) ↔
        ∀ p ∈ v 7, p ∈ forcingFormula (v 7) (v 8) φ
          (standardTuple ![checkName ⟨v 2, v 5⟩ₖ (v 6)]))) := by
  simp [twoStepCheckedTransferFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_eq_args3, forall_eq_args4,
    forall_eq_args5, forall_eq_args6]

theorem twoStep_checked_forcing {P R Q S t one a : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (φ : SetTheorySemisentence 1) :
    (∀ p ∈ P, p ∈ forcingFormula P R (allCheckedForcingFormula φ)
      (standardTuple ![Q, S, t, checkName one a])) ↔
    (∀ p ∈ twoStepConditions P R Q t,
      p ∈ forcingFormula (twoStepConditions P R Q t) (twoStepOrder P R Q S t) φ
        (standardTuple ![checkName ⟨one, t⟩ₖ a])) := by
  have hh := eval_of_countable_zf (twoStepCheckedTransferFormula φ) (by
    intro W _ _ _ _ v
    apply (eval_twoStepCheckedTransferFormula φ v).mpr
    intro hR ht h hC hT
    rw [hC, hT]
    exact twoStep_checked_forcing_countable hR ht h φ)
    ![P, R, one, Q, S, t, a, twoStepConditions P R Q t, twoStepOrder P R Q S t]
  exact (eval_twoStepCheckedTransferFormula φ
    ![P, R, one, Q, S, t, a, twoStepConditions P R Q t, twoStepOrder P R Q S t]).mp hh
      hR htop h rfl rfl

end ZFVP
