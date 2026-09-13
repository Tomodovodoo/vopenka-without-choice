import ZFVP.SetTheory.CnAbsoluteness
import ZFVP.Syntax.BoundedStandardTuples
import ZFVP.Syntax.DeltaOneMembershipTruth
import ZFVP.Syntax.StandardCodeExpressions

/-! Relativizing a fixed external formula to a set domain.

For a fixed formula `φ` with `n` free variables, `satisfiesAtFormula φ` is a single formula with
`n + 1` free variables saying that the domain named by the first variable satisfies `φ` at the
remaining variables. Its Levy level is Pi-1 no matter how complicated `φ` is, because the numeral,
the code of `φ` and the parameter tuple are all quantified boundedly inside the domain. At a
`C(k+1)` rank stage the relativized form agrees with the real relation defined by `φ` whenever `φ`
is Levy of level `k + 1`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Free variable `0` is the domain, free variables `1, …, n` are the parameters. -/
def satisfiesAtFormula {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  boundedSetExs (.bvar 0) (((boundedNumeralFormula n).subst ![.bvar 0]).and
    (boundedSetExs (.bvar 1) (((membershipFormulaExpression φ).formula.subst ![.bvar 2, .bvar 0]).and
      (boundedSetExs (.bvar 2) (((boundedStandardTupleFormula n).subst
          (.bvar 3 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ)).and
        (piOneMembershipTruthFormula.subst ![.bvar 3, .bvar 2, .bvar 1, .bvar 0]))))))

theorem satisfiesAtFormula_piOne {n : ℕ} (φ : SetTheorySemisentence n) :
    IsPiFormula 1 (satisfiesAtFormula φ) :=
  .boundedExs (.bvar 0) (.and (.bounded ((boundedNumeralFormula_bounded n).subst _))
    (.boundedExs (.bvar 1) (.and (.bounded ((membershipFormulaExpression φ).formula_bounded.subst _))
      (.boundedExs (.bvar 2) (.and (.bounded ((boundedStandardTupleFormula_bounded n).subst _))
        (piOneMembershipTruthFormula_piOne.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

/-- The relativized formula names internal satisfaction over the domain. -/
theorem eval_satisfiesAtFormula_iff_satisfies {n : ℕ} (φ : SetTheorySemisentence n) {A : V}
    [hA : IsSequenceSupport A] (v : Fin n → V) (hv : ∀ i, v i ∈ A) :
    (satisfiesAtFormula φ).Evalb (A :> v) ↔
      MembershipSatisfies A (n : V) (encodeMembershipFormula φ) (standardTuple v) := by
  have hc : encodeMembershipFormula φ ∈ A := by
    simpa using (membershipFormulaExpression φ).eval_mem (![] : Fin 0 → V) (Fin.elim0 ·)
  have ht : standardTuple v ∈ A := standardTuple_mem_support v hv
  simp [satisfiesAtFormula, eval_boundedSetExs, eval_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_boundedStandardTupleFormula, IsCodingSupport.numeral_mem, hc, ht, hv,
    (membershipFormulaExpression φ).eval_formula (U := A) (![] : Fin 0 → V) (Fin.elim0 ·)]

theorem eval_satisfiesAtFormula {n : ℕ} (φ : SetTheorySemisentence n) (A : V)
    (hA : IsSequenceSupport A) (v : Fin n → SetDomain A) :
    (satisfiesAtFormula φ).Evalb (A :> fun i ↦ (v i).val) ↔ φ.Evalb v := by
  let := hA
  have hne : IsNonempty A := ⟨⟨∅, IsCodingSupport.empty_mem⟩⟩
  rw [eval_satisfiesAtFormula_iff_satisfies φ (fun i ↦ (v i).val) (fun i ↦ (v i).property)]
  exact membershipSatisfies_encode hne φ v

/-- At a `C(k+1)` rank stage the Pi-1 relativized form of a Levy `k+1` formula computes the
relation the formula defines. -/
theorem satisfiesAtFormula_iff_defined {p : LevyPolarity} {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula p (k + 1) φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    (satisfiesAtFormula φ).Evalb (hierarchy δ :> v) ↔ R v := by
  have hs : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let w : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hw : (fun i ↦ (w i).val) = v := rfl
  calc (satisfiesAtFormula φ).Evalb (hierarchy δ :> v)
      ↔ φ.Evalb w := by rw [← hw]; exact eval_satisfiesAtFormula φ (hierarchy δ) hs w
    _ ↔ R v := hδ.defined_correct hφ R w

end ZFVP
