import ZFVP.SetTheory.BoundedCodingSupport

/-! Finite constructor expressions have bounded relational definitions inside coding supports. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive CodeExpression (n : ℕ)
  | var : Fin n → CodeExpression n
  | num : ℕ → CodeExpression n
  | kpair : CodeExpression n → CodeExpression n → CodeExpression n
  | doubleton : CodeExpression n → CodeExpression n → CodeExpression n
  | succ : CodeExpression n → CodeExpression n

namespace CodeExpression

def binaryFormula {n : ℕ} (R : SetTheorySemisentence 3)
    (φ ψ : SetTheorySemisentence (n + 2)) : SetTheorySemisentence (n + 2) :=
  boundedSetExs (.bvar 0) (boundedSetExs (.bvar 1)
    ((φ.subst (.bvar 2 :> .bvar 1 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ)).and
      ((ψ.subst (.bvar 2 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ)).and
        (R.subst ![.bvar 3, .bvar 1, .bvar 0]))))

def unaryFormula {n : ℕ} (R : SetTheorySemisentence 2)
    (φ : SetTheorySemisentence (n + 2)) : SetTheorySemisentence (n + 2) :=
  boundedSetExs (.bvar 0)
    ((φ.subst (.bvar 1 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ)).and
      (R.subst ![.bvar 2, .bvar 0]))

def formula {n : ℕ} : CodeExpression n → SetTheorySemisentence (n + 2)
  | .var i => .rel Language.Set.Rel.eq ![.bvar 1, .bvar i.succ.succ]
  | .num k => boundedNumeralFormula k |>.subst ![.bvar 1]
  | .kpair t u => binaryFormula boundedKpairFormula t.formula u.formula
  | .doubleton t u => binaryFormula boundedDoubletonFormula t.formula u.formula
  | .succ t => unaryFormula boundedSuccFormula t.formula

theorem binaryFormula_bounded {n : ℕ} {R : SetTheorySemisentence 3}
    {φ ψ : SetTheorySemisentence (n + 2)} (hR : IsBoundedSetFormula R)
    (hφ : IsBoundedSetFormula φ) (hψ : IsBoundedSetFormula ψ) :
    IsBoundedSetFormula (binaryFormula R φ ψ) :=
  .exs (.bvar 0) (.exs (.bvar 1) (.and (hφ.subst _) (.and (hψ.subst _) (hR.subst _))))

theorem unaryFormula_bounded {n : ℕ} {R : SetTheorySemisentence 2}
    {φ : SetTheorySemisentence (n + 2)} (hR : IsBoundedSetFormula R)
    (hφ : IsBoundedSetFormula φ) : IsBoundedSetFormula (unaryFormula R φ) :=
  .exs (.bvar 0) (.and (hφ.subst _) (hR.subst _))

theorem formula_bounded {n : ℕ} (t : CodeExpression n) : IsBoundedSetFormula t.formula := by
  induction t with
  | var i => exact .rel _ _
  | num k => exact (boundedNumeralFormula_bounded k).subst _
  | kpair t u iht ihu => exact binaryFormula_bounded boundedKpairFormula_bounded iht ihu
  | doubleton t u iht ihu => exact binaryFormula_bounded boundedDoubletonFormula_bounded iht ihu
  | succ t iht => exact unaryFormula_bounded boundedSuccFormula_bounded iht

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

noncomputable def eval {n : ℕ} (v : Fin n → V) : CodeExpression n → V
  | .var i => v i
  | .num k => k
  | .kpair t u => ⟨t.eval v, u.eval v⟩ₖ
  | .doubleton t u => SetTheory.doubleton (t.eval v) (u.eval v)
  | .succ t => SetTheory.succ (t.eval v)

theorem eval_mem {n : ℕ} (t : CodeExpression n) {U : V} [hU : IsCodingSupport U]
    (v : Fin n → V) (hv : ∀ i, v i ∈ U) : t.eval v ∈ U := by
  induction t with
  | var i => exact hv i
  | num k => exact IsCodingSupport.numeral_mem k
  | kpair t u iht ihu => exact hU.kpair_closed _ iht _ ihu
  | doubleton t u iht ihu => exact hU.doubleton_closed _ iht _ ihu
  | succ t iht => exact hU.succ_closed _ iht

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_binaryFormula {n : ℕ} (R : SetTheorySemisentence 3)
    (φ ψ : SetTheorySemisentence (n + 2)) (U y : V) (v : Fin n → V) :
    (binaryFormula R φ ψ).Evalb (U :> y :> v) ↔
      ∃ a ∈ U, ∃ b ∈ U, φ.Evalb (U :> a :> v) ∧ ψ.Evalb (U :> b :> v) ∧ R.Evalb ![y, a, b] := by
  simp [binaryFormula, eval_boundedSetExs, eval_and, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_unaryFormula {n : ℕ} (R : SetTheorySemisentence 2)
    (φ : SetTheorySemisentence (n + 2)) (U y : V) (v : Fin n → V) :
    (unaryFormula R φ).Evalb (U :> y :> v) ↔
      ∃ a ∈ U, φ.Evalb (U :> a :> v) ∧ R.Evalb ![y, a] := by
  simp [unaryFormula, eval_boundedSetExs, eval_and, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem eval_formula {n : ℕ} (t : CodeExpression n) {U : V} [IsCodingSupport U]
    (v : Fin n → V) (hv : ∀ i, v i ∈ U) (y : V) :
    t.formula.Evalb (U :> y :> v) ↔ y = t.eval v := by
  induction t generalizing y with
  | var i => simp [formula, eval, Structure.rel]
  | num k => simp [formula, eval]
  | kpair t u iht ihu =>
    simp only [formula, eval_binaryFormula, iht, ihu]
    simp [eval, t.eval_mem v hv, u.eval_mem v hv]
  | doubleton t u iht ihu =>
    simp only [formula, eval_binaryFormula, iht, ihu]
    simp [eval, t.eval_mem v hv, u.eval_mem v hv]
  | succ t iht =>
    simp only [formula, eval_unaryFormula, iht]
    simp [eval, t.eval_mem v hv]

theorem eval_formula_iff {n : ℕ} (t : CodeExpression n) (w : Fin (n + 2) → V)
    [IsCodingSupport (w 0)] (hw : ∀ i : Fin n, w i.succ.succ ∈ w 0) :
    t.formula.Evalb w ↔ w 1 = t.eval (fun i ↦ w i.succ.succ) := by
  have he : w = w 0 :> w 1 :> fun i : Fin n ↦ w i.succ.succ := by
    ext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i <;> simp
  conv_lhs => rw [he]
  exact t.eval_formula _ hw _

@[simp] theorem eval_formula_zero (t : CodeExpression 0) (U y : V) [IsCodingSupport U] :
    t.formula.Evalb ![U, y] ↔ y = t.eval ![] := t.eval_formula ![] (Fin.elim0 ·) y

@[simp] theorem eval_formula_one (t : CodeExpression 1) (U y x : V) [IsCodingSupport U]
    (hx : x ∈ U) : t.formula.Evalb ![U, y, x] ↔ y = t.eval ![x] :=
  t.eval_formula ![x] (by simpa using hx) y

@[simp] theorem eval_formula_two (t : CodeExpression 2) (U y x z : V) [IsCodingSupport U]
    (hx : x ∈ U) (hz : z ∈ U) : t.formula.Evalb ![U, y, x, z] ↔ y = t.eval ![x, z] :=
  t.eval_formula ![x, z] (by simpa using And.intro hx hz) y

end CodeExpression
end ZFVP
