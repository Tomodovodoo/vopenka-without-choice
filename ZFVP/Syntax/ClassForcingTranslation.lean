import ZFVP.Syntax.LevyForcingSteps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Parameter-free formulas defining the carrier, order, names, and atomic
forcing clauses. The carrier itself need not be a set of the evaluating model. -/
structure ClassForcingDictionary where
  carrier : SetTheorySemisentence 1
  order : SetTheorySemisentence 2
  names : SetTheorySemisentence 1
  base : {n : ℕ} → BoundedFormulaTree n → SetTheorySemisentence (n + 1)

namespace ClassForcingDictionary

def orStep (d : ClassForcingDictionary) {n : ℕ}
    (φ ψ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (n + 1) :=
  (d.carrier.subst ![.bvar 0]).and
    (.all ((∼(d.carrier.subst ![.bvar 0])).or
      ((∼(d.order.subst ![.bvar 0, .bvar 1])).or
        (.exs ((d.carrier.subst ![.bvar 0]).and
          ((d.order.subst ![.bvar 0, .bvar 1]).and
            ((φ.subst (.bvar 0 :> forcingParameterTerms 3 rfl)).or
              (ψ.subst (.bvar 0 :> forcingParameterTerms 3 rfl)))))))))

def allStep (d : ClassForcingDictionary) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) : SetTheorySemisentence (n + 1) :=
  (d.carrier.subst ![.bvar 0]).and
    (.all ((∼(d.names.subst ![.bvar 0])).or
      (φ.subst (.bvar 1 :> .bvar 0 :> forcingParameterTerms 2 rfl))))

def exsStep (d : ClassForcingDictionary) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) : SetTheorySemisentence (n + 1) :=
  (d.carrier.subst ![.bvar 0]).and
    (.all ((∼(d.carrier.subst ![.bvar 0])).or
      ((∼(d.order.subst ![.bvar 0, .bvar 1])).or
        (.exs ((d.carrier.subst ![.bvar 0]).and
          ((d.order.subst ![.bvar 0, .bvar 1]).and
            (.exs ((d.names.subst ![.bvar 0]).and
              (φ.subst (.bvar 1 :> .bvar 0 :> forcingParameterTerms 4 rfl))))))))))

def translation (d : ClassForcingDictionary) : {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence (n + 1)
  | _, .verum => d.carrier.subst ![.bvar 0]
  | _, .falsum => .falsum
  | _, .rel r ts => d.base (.rel r ts)
  | _, .nrel r ts => d.base (.nrel r ts)
  | _, .and φ ψ => (d.translation φ).and (d.translation ψ)
  | _, .or φ ψ => d.orStep (d.translation φ) (d.translation ψ)
  | _, .all φ => d.allStep (d.translation φ)
  | _, .exs φ => d.exsStep (d.translation φ)

variable {M : Type*} [SetStructure M]

private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → M) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → M) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl
private theorem eval_all {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → M) :
    φ.all.Evalb v ↔ ∀ x : M, φ.Evalb (x :> v) := Iff.rfl
private theorem eval_exs {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → M) :
    φ.exs.Evalb v ↔ ∃ x : M, φ.Evalb (x :> v) := Iff.rfl
@[simp] theorem eval_orStep (d : ClassForcingDictionary) {n : ℕ}
    (φ ψ : SetTheorySemisentence (n + 1)) (p : M) (v : Fin n → M) :
    (d.orStep φ ψ).Evalb (p :> v) ↔
      d.carrier.Evalb ![p] ∧ ∀ q : M, d.carrier.Evalb ![q] → d.order.Evalb ![q, p] →
        ∃ r : M, d.carrier.Evalb ![r] ∧ d.order.Evalb ![r, q] ∧
          (φ.Evalb (r :> v) ∨ ψ.Evalb (r :> v)) := by
  simp [orStep, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, eval_and, eval_or, eval_all, eval_exs, ← imp_iff_not_or]

@[simp] theorem eval_allStep (d : ClassForcingDictionary) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) (p : M) (v : Fin n → M) :
    (d.allStep φ).Evalb (p :> v) ↔
      d.carrier.Evalb ![p] ∧ ∀ u : M, d.names.Evalb ![u] → φ.Evalb (p :> u :> v) := by
  simp [allStep, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, eval_and, eval_or, eval_all, eval_exs, ← imp_iff_not_or]

@[simp] theorem eval_exsStep (d : ClassForcingDictionary) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) (p : M) (v : Fin n → M) :
    (d.exsStep φ).Evalb (p :> v) ↔
      d.carrier.Evalb ![p] ∧ ∀ q : M, d.carrier.Evalb ![q] → d.order.Evalb ![q, p] →
        ∃ r : M, d.carrier.Evalb ![r] ∧ d.order.Evalb ![r, q] ∧
          ∃ u : M, d.names.Evalb ![u] ∧ φ.Evalb (r :> u :> v) := by
  simp [exsStep, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, eval_and, eval_or, eval_all, eval_exs, ← imp_iff_not_or]

end ClassForcingDictionary
end ZFVP


