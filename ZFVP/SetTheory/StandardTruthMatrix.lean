import ZFVP.Syntax.StandardCodeExpressions
import ZFVP.Syntax.BoundedStandardTuples
import ZFVP.Syntax.BoundedMembershipTruthCertificate
import ZFVP.SetTheory.HigherPartialTruth

/-! A single support set bounds the syntax and assignment witnesses of partial truth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def standardTruthMatrix {n : ℕ} (D : SetTheorySemisentence 1)
    (T : SetTheorySemisentence 5) (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  (sequenceSupportFormula.subst ![.bvar 0]).and
    (boundedSetExs (.bvar 0) ((D.subst ![.bvar 0]).and
      (boundedSetExs (.bvar 1) (((boundedNumeralFormula n).subst ![.bvar 0]).and
        (boundedSetExs (.bvar 2) (((membershipFormulaExpression φ).formula.subst ![.bvar 3, .bvar 0]).and
          (boundedSetExs (.bvar 3)
            (((boundedStandardTupleFormula n).subst (.bvar 4 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ)).and
              ((boundedFunctionFormula.subst ![.bvar 0, .bvar 2, .bvar 3]).and
                (T.subst ![.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]))))))))))

theorem standardTruthMatrix_levy {n k : ℕ} {p : LevyPolarity}
    {D : SetTheorySemisentence 1} {T : SetTheorySemisentence 5}
    (hD : IsLevyFormula p k D) (hT : IsLevyFormula p k T) (φ : SetTheorySemisentence n) :
    IsLevyFormula p k (standardTruthMatrix D T φ) :=
  .and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.boundedExs (.bvar 0) (.and (hD.subst _)
      (.boundedExs (.bvar 1) (.and (.bounded ((boundedNumeralFormula_bounded n).subst _))
        (.boundedExs (.bvar 2) (.and (.bounded ((membershipFormulaExpression φ).formula_bounded.subst _))
          (.boundedExs (.bvar 3) (.and (.bounded ((boundedStandardTupleFormula_bounded n).subst _))
            (.and (.bounded (boundedFunctionFormula_bounded.subst _)) (hT.subst _))))))))))

theorem standardTruthMatrix_bounded {n : ℕ} {D : SetTheorySemisentence 1}
    {T : SetTheorySemisentence 5} (hD : IsBoundedSetFormula D) (hT : IsBoundedSetFormula T)
    (φ : SetTheorySemisentence n) : IsBoundedSetFormula (standardTruthMatrix D T φ) :=
  .and (sequenceSupportFormula_bounded.subst _)
    (.exs (.bvar 0) (.and (hD.subst _)
      (.exs (.bvar 1) (.and ((boundedNumeralFormula_bounded n).subst _)
        (.exs (.bvar 2) (.and ((membershipFormulaExpression φ).formula_bounded.subst _)
          (.exs (.bvar 3) (.and ((boundedStandardTupleFormula_bounded n).subst _)
            (.and (boundedFunctionFormula_bounded.subst _) (hT.subst _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_standardTruthMatrix {n : ℕ} (D : SetTheorySemisentence 1)
    (T : SetTheorySemisentence 5) (φ : SetTheorySemisentence n) (U : V) (v : Fin n → V) :
    (standardTruthMatrix D T φ).Evalb (U :> v) ↔
      IsSequenceSupport U ∧ ∃ A ∈ U, D.Evalb ![A] ∧
        standardTuple v ∈ A ^ (n : V) ∧
          T.Evalb ![U, A, (n : V), encodeMembershipFormula φ, standardTuple v] := by
  simp only [standardTruthMatrix, eval_and, Semiformula.eval_substs]
  simp only [Function.comp_def]
  rw [Defined.eval_iff]
  apply and_congr_right
  intro hU
  change IsSequenceSupport U at hU
  let := hU
  have hc : encodeMembershipFormula φ ∈ U := by
    simpa using (membershipFormulaExpression φ).eval_mem (![] : Fin 0 → V) (Fin.elim0 ·)
  simp [eval_boundedSetExs, eval_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_boundedStandardTupleFormula, IsCodingSupport.numeral_mem, hc]
  apply exists_congr
  intro A
  apply and_congr_right
  intro hA
  apply and_congr_right
  intro hD
  constructor
  · intro h
    exact h.2.2
  · rintro ⟨hb, ht⟩
    have hv : ∀ i, v i ∈ U := fun i ↦ hU.mem_trans (standardTuple_values_mem v hb i) hA
    exact ⟨standardTuple_mem_support v hv, hv, hb, ht⟩

end ZFVP
