import ZFVP.Syntax.BoundedConstructorExpressions

/-! Bounded lookup in a truth table at a constructed formula-context code. -/

namespace ZFVP.CodeExpression

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lookupFormula {n : ℕ} (t : CodeExpression n) : SetTheorySemisentence (n + 3) :=
  boundedSetExs (.bvar 0)
    ((t.formula.subst (.bvar 1 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ)).and
      (boundedPairMemberFormula.subst ![.bvar 2, .bvar 0, .bvar 3]))

theorem lookupFormula_bounded {n : ℕ} (t : CodeExpression n) : IsBoundedSetFormula t.lookupFormula :=
  .exs (.bvar 0) (.and (t.formula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_lookupFormula {n : ℕ} (t : CodeExpression n) {U : V} [IsCodingSupport U]
    (T b : V) (v : Fin n → V) (hv : ∀ i, v i ∈ U) :
    t.lookupFormula.Evalb (U :> T :> b :> v) ↔ ⟨t.eval v, b⟩ₖ ∈ T := by
  have hand {k : ℕ} (φ ψ : SetTheorySemisentence k) (w : Fin k → V) :
      (φ.and ψ).Evalb w ↔ φ.Evalb w ∧ ψ.Evalb w := Iff.rfl
  simp [lookupFormula, eval_boundedSetExs, hand, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  simp only [t.eval_formula v hv]
  simp [t.eval_mem v hv]

@[simp] theorem eval_lookupFormula_one (t : CodeExpression 1) {U x : V} [IsCodingSupport U]
    (T b : V) (hx : x ∈ U) : t.lookupFormula.Evalb ![U, T, b, x] ↔ ⟨t.eval ![x], b⟩ₖ ∈ T :=
  t.eval_lookupFormula T b ![x] (by simpa using hx)

@[simp] theorem eval_lookupFormula_two (t : CodeExpression 2) {U x y : V} [IsCodingSupport U]
    (T b : V) (hx : x ∈ U) (hy : y ∈ U) :
    t.lookupFormula.Evalb ![U, T, b, x, y] ↔ ⟨t.eval ![x, y], b⟩ₖ ∈ T :=
  t.eval_lookupFormula T b ![x, y] (by simpa using And.intro hx hy)

@[simp] theorem eval_lookupFormula_three (t : CodeExpression 3) {U x y z : V} [IsCodingSupport U]
    (T b : V) (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U) :
    t.lookupFormula.Evalb ![U, T, b, x, y, z] ↔ ⟨t.eval ![x, y, z], b⟩ₖ ∈ T :=
  t.eval_lookupFormula T b ![x, y, z] (by
    simp only [Fin.forall_fin_iff_zero_and_forall_succ]
    simpa using And.intro hx (And.intro hy hz))

end ZFVP.CodeExpression
