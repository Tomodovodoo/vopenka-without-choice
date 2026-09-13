import ZFVP.ModelTheory.ForcingModel
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.SetTheory.ElementaryForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def functionValueFormula : SetTheorySemisentence 3 :=
  f“f a x. !IsFunction.dfn f ∧ !value.dfn x f a”

def checkedTripleForcingFormula (φ : SetTheorySemisentence 3) : SetTheorySemisentence 7 :=
  f“P R o t p a x. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o x))
        (!checkNameFormula o a)) t)”

def checkedFunctionValueDecisionFormula : SetTheorySemisentence 7 :=
  checkedTripleForcingFormula functionValueFormula

def checkedFunctionValueUniqueFormula : SetTheorySemisentence 8 :=
  f“P R o t p a x y. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P t ∧ !checkedFunctionValueDecisionFormula P R o t p a x ∧
    !checkedFunctionValueDecisionFormula P R o t p a y → x = y”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_functionValueFormula (v : Fin 3 → V) :
    functionValueFormula.Evalb v ↔ IsFunction (v 0) ∧ (v 0) ‘ (v 1) = v 2 := by
  simp [functionValueFormula, eq_comm]

def ForcesCheckedFunctionValue (P R one τ p a x : V) : Prop :=
  p ∈ forcingFormula P R functionValueFormula
    (standardTuple ![τ, checkName one a, checkName one x])

instance forcesCheckedFunctionValue_definable (P R one τ : V) :
    ℒₛₑₜ-relation₃[V] (ForcesCheckedFunctionValue P R one τ) := by
  unfold ForcesCheckedFunctionValue
  simp only [standardTuple]
  definability

instance checkedTripleForcingFormula_defined (φ : SetTheorySemisentence 3) :
    Defined (fun v : Fin 7 → V ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![v 3, checkName (v 2) (v 5), checkName (v 2) (v 6)]))
      (checkedTripleForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [checkedTripleForcingFormula, standardTuple,
      Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

instance checkedFunctionValueDecisionFormula_defined :
    Defined (fun v : Fin 7 → V ↦ ForcesCheckedFunctionValue (v 0) (v 1) (v 2)
      (v 3) (v 4) (v 5) (v 6)) checkedFunctionValueDecisionFormula :=
  checkedTripleForcingFormula_defined functionValueFormula

theorem eval_checkedFunctionValueUniqueFormula (v : Fin 8 → V) :
    checkedFunctionValueUniqueFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) →
      ForcesCheckedFunctionValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) →
      ForcesCheckedFunctionValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7) → v 6 = v 7) := by
  simp [checkedFunctionValueUniqueFormula]

namespace ForcingContext

theorem formula_truth (S : ForcingContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName S.P) :
    φ.Evalb (fun i ↦ S.ofName (v i)) ↔
      GenericMeets S.G (forcingFormula S.P S.R φ (standardTuple (fun i ↦ (v i).val))) :=
  forcingFormula_quotient_truth S.P S.R S.G S.order S.generic φ v

theorem checkedFunctionValue_truth (S : ForcingContext V) (τ : ForcingName S.P) (a x : V) :
    (∃ p ∈ S.G, ForcesCheckedFunctionValue S.P S.R S.one τ.val p a x) ↔
      IsFunction (S.ofName τ) ∧ (S.ofName τ) ‘ (S.check a) = S.check x := by
  let ν : ForcingName S.P := ⟨checkName S.one a, checkName_isName S.top.1 a⟩
  let σ : ForcingName S.P := ⟨checkName S.one x, checkName_isName S.top.1 x⟩
  let v : Fin 3 → ForcingName S.P := ![τ, ν, σ]
  exact (S.formula_truth functionValueFormula v).symm.trans (eval_functionValueFormula _)

end ForcingContext

theorem forcesCheckedFunctionValue_unique_countable [Countable V] {P R one τ p a x y : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hx : ForcesCheckedFunctionValue P R one τ p a x)
    (hy : ForcesCheckedFunctionValue P R one τ p a y) : x = y := by
  have hp : p ∈ P := (forcingFormula_regular hR functionValueFormula _).1 p hx
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hfx := (S.checkedFunctionValue_truth ⟨τ, hτ⟩ a x).mp ⟨p, hpG, hx⟩
  have hfy := (S.checkedFunctionValue_truth ⟨τ, hτ⟩ a y).mp ⟨p, hpG, hy⟩
  exact (S.check_eq_iff x y).mp (hfx.2.symm.trans hfy.2)

theorem forcesCheckedFunctionValue_unique {P R one τ p a x y : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hx : ForcesCheckedFunctionValue P R one τ p a x)
    (hy : ForcesCheckedFunctionValue P R one τ p a y) : x = y := by
  have hh := eval_of_countable_zf checkedFunctionValueUniqueFormula (by
    intro W _ _ _ _ v
    exact (eval_checkedFunctionValueUniqueFormula v).mpr
      (fun hR htop hτ hx hy ↦ forcesCheckedFunctionValue_unique_countable hR htop hτ hx hy))
    ![P, R, one, τ, p, a, x, y]
  exact (eval_checkedFunctionValueUniqueFormula _).mp hh hR htop hτ hx hy

end ZFVP


