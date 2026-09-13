import ZFVP.ModelTheory.SparseBoundedForcingBase
import ZFVP.SetTheory.FormulaStructuralHeight

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
set_option maxHeartbeats 20000

def sparseAtomicSyntaxDictionary : SetFormulaDictionary :=
  [⟨1, boundedEmptyFormula⟩, ⟨2, boundedSuccFormula⟩, ⟨3, boundedKpairFormula⟩,
   ⟨3, boundedDoubletonFormula⟩, ⟨1, isEmpty⟩, ⟨2, succ.dfn⟩,
   ⟨2, codingUniverseFormula⟩, ⟨1, sequenceSupportFormula⟩,
   ⟨3, boundedFunctionFormula⟩, ⟨3, boundedPairMemberFormula⟩,
   ⟨4, woodinSparseLocalForcingFormula⟩]

private structure AtomicSyntaxBound (D : SetFormulaDictionary) where
  level : ℕ
  exactValue : level = levyDictionaryBound D + 100
  ge : 100 ≤ level
  bound : ∀ φ ∈ D, levySyntacticBound φ.2 ≤ level

private def makeAtomicSyntaxBound (D : SetFormulaDictionary) : AtomicSyntaxBound D where
  level := levyDictionaryBound D + 100
  exactValue := rfl
  ge := Nat.le_add_left 100 (levyDictionaryBound D)
  bound := fun φ hφ ↦ Nat.le_add_right_of_le (levySyntacticBound_le_dictionaryBound D φ hφ)

private opaque atomicSyntaxBound : AtomicSyntaxBound sparseAtomicSyntaxDictionary :=
  makeAtomicSyntaxBound sparseAtomicSyntaxDictionary

/-- A fixed coefficient absorbing every graph formula in the atomic compiler. -/
def sparseAtomicSyntaxConstant : ℕ := atomicSyntaxBound.level

theorem sparseAtomicSyntaxConstant_eq : sparseAtomicSyntaxConstant =
    levyDictionaryBound sparseAtomicSyntaxDictionary + 100 := atomicSyntaxBound.exactValue

private theorem atomic_graph_bound {n} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ sparseAtomicSyntaxDictionary) :
    levySyntacticBound φ ≤ sparseAtomicSyntaxConstant :=
  atomicSyntaxBound.bound ⟨n, φ⟩ hφ

theorem sparseAtomicSyntaxConstant_ge : 100 ≤ sparseAtomicSyntaxConstant := atomicSyntaxBound.ge

private theorem bound_bexs {n} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n+1)) :
    levySyntacticBound (Semiformula.bexsMem t φ) = levySyntacticBound φ + 2 := by
  change max 0 (levySyntacticBound φ) + 2 = _
  simp

private theorem bound_nest_zero {m} (φ : SetTheorySemisentence 1) :
    levySyntacticBound (Semiformula.nestFormulaeFunc φ (![] : Fin 0 → SetTheorySemisentence (m+1))) =
      levySyntacticBound φ := by
  unfold Semiformula.nestFormulaeFunc
  simp only [allItr_zero, Matrix.conj, Semiformula.imp_eq, levySyntacticBound,
    levySyntacticBound_neg, levySyntacticBound_rew, Nat.zero_max]

private theorem bound_nest_one {m} (φ : SetTheorySemisentence 2) (ψ : SetTheorySemisentence (m+1)) :
    levySyntacticBound (Semiformula.nestFormulaeFunc φ ![ψ]) =
      max (levySyntacticBound ψ) (levySyntacticBound φ) + 2 := by
  unfold Semiformula.nestFormulaeFunc
  simp only [allItr_succ, allItr_zero, Matrix.conj, Semiformula.imp_eq, levySyntacticBound,
    levySyntacticBound_neg, levySyntacticBound_rew, Nat.max_zero, Matrix.cons_val_zero]

private theorem bound_nest_two {m} (φ : SetTheorySemisentence 2)
    (ψ χ : SetTheorySemisentence (m+1)) :
    levySyntacticBound (Semiformula.nestFormulae φ ![ψ,χ]) =
      max (max (levySyntacticBound ψ) (levySyntacticBound χ)) (levySyntacticBound φ) + 4 := by
  unfold Semiformula.nestFormulae
  simp only [allItr_succ, allItr_zero, Matrix.conj, Semiformula.imp_eq, levySyntacticBound,
    levySyntacticBound_neg, levySyntacticBound_rew, Nat.max_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.vecTail, Function.comp_def, Nat.add_assoc, Nat.reduceAdd]

private theorem bound_equal {n} (s t : SetTheorySemiterm Empty n) :
    levySyntacticBound (op(=).operator ![s,t]) = 0 := rfl

private theorem bound_rawNeg {n} (φ : SetTheorySemisentence n) :
    levySyntacticBound φ.neg = levySyntacticBound φ := levySyntacticBound_neg φ

private theorem bound_boundedNumeral (n : ℕ) :
    levySyntacticBound (boundedNumeralFormula n) ≤ sparseAtomicSyntaxConstant + 2 * n := by
  induction n with
  | zero => simpa [boundedNumeralFormula] using
      (atomic_graph_bound (φ := boundedEmptyFormula) (by simp [sparseAtomicSyntaxDictionary]))
  | succ n ih =>
    simp only [boundedNumeralFormula, bound_bexs, levySyntacticBound, levySyntacticBound_rew]
    have hc : levySyntacticBound boundedSuccFormula ≤ sparseAtomicSyntaxConstant := by
      exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
    omega

private theorem bound_numeral (n : ℕ) :
    levySyntacticBound (numeralFormula n) ≤ sparseAtomicSyntaxConstant + 6 * n := by
  induction n with
  | zero => simpa [numeralFormula] using
      (atomic_graph_bound (φ := isEmpty) (by simp [sparseAtomicSyntaxDictionary]))
  | succ n ih =>
    simp only [numeralFormula, levySyntacticBound, levySyntacticBound_neg, bound_rawNeg,
      levySyntacticBound_rew, bound_nest_zero, bound_nest_one, bound_equal]
    have hc : levySyntacticBound succ.dfn ≤ sparseAtomicSyntaxConstant := by
      exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
    omega

private def expressionDepth {n} : CodeExpression n → ℕ
  | .var _ => 0
  | .num k => k
  | .kpair x y | .doubleton x y => max (expressionDepth x) (expressionDepth y) + 1
  | .succ x => expressionDepth x + 1

private theorem bound_expression {n} (e : CodeExpression n) :
    levySyntacticBound e.formula ≤ sparseAtomicSyntaxConstant + 4 * expressionDepth e := by
  induction e with
  | var i => simp [CodeExpression.formula, expressionDepth, levySyntacticBound]
  | num k =>
    simp only [CodeExpression.formula, levySyntacticBound_rew, expressionDepth]
    have h := bound_boundedNumeral k
    omega
  | kpair x y ihx ihy =>
    simp only [CodeExpression.formula, CodeExpression.binaryFormula, boundedSetExs,
      levySyntacticBound, levySyntacticBound_rew, expressionDepth]
    have hc : levySyntacticBound boundedKpairFormula ≤ sparseAtomicSyntaxConstant := by
      exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
    omega
  | doubleton x y ihx ihy =>
    simp only [CodeExpression.formula, CodeExpression.binaryFormula, boundedSetExs,
      levySyntacticBound, levySyntacticBound_rew, expressionDepth]
    have hc : levySyntacticBound boundedDoubletonFormula ≤ sparseAtomicSyntaxConstant := by
      exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
    omega
  | succ x ih =>
    simp only [CodeExpression.formula, CodeExpression.unaryFormula, boundedSetExs,
      levySyntacticBound, levySyntacticBound_rew, expressionDepth]
    have hc : levySyntacticBound boundedSuccFormula ≤ sparseAtomicSyntaxConstant := by
      exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
    omega

private theorem expressionDepth_atom {n a} (r : Language.Set.Rel a)
    (ts : Fin a → SetTheorySemiterm Empty n) :
    expressionDepth (membershipFormulaExpression (.rel r ts)) ≤ n + 10 ∧
    expressionDepth (membershipFormulaExpression (.nrel r ts)) ≤ n + 10 := by
  cases r <;>
    simp only [membershipFormulaExpression, membershipArgumentExpression, membershipRelationIndex,
      CodeExpression.atom, CodeExpression.negAtom, CodeExpression.relation, CodeExpression.boundArgs,
      CodeExpression.tuple₂, CodeExpression.boundVar, expressionDepth]
  all_goals
    have h0 := (membershipTermIndex (ts 0)).isLt
    have h1 := (membershipTermIndex (ts 1)).isLt
    omega

private theorem bound_closedExpression (e : CodeExpression 0) :
    levySyntacticBound (closedCodeExpressionFormula e) ≤
      sparseAtomicSyntaxConstant + 4 * expressionDepth e + 6 := by
  have he := bound_expression e
  have hc : levySyntacticBound codingUniverseFormula ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
  have h0 : levySyntacticBound isEmpty ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
  simp only [closedCodeExpressionFormula, bound_nest_two, bound_nest_zero, bound_nest_one,
    levySyntacticBound, levySyntacticBound_neg, bound_rawNeg, levySyntacticBound_rew, bound_equal]
  omega

private theorem bound_tupleEntry {n} (i : Fin n) :
    levySyntacticBound (standardTupleEntryFormula i) ≤ sparseAtomicSyntaxConstant + 2 * n + 2 := by
  have hi := bound_boundedNumeral i.val
  have hc : levySyntacticBound boundedPairMemberFormula ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
  simp only [standardTupleEntryFormula, boundedSetExs, levySyntacticBound, levySyntacticBound_rew]
  have hin := i.isLt
  omega

private theorem bound_finiteConjunction {n k B} (f : Fin k → SetTheorySemisentence n)
    (hf : ∀ i, levySyntacticBound (f i) ≤ B) : levySyntacticBound (finiteConjunction f) ≤ B := by
  induction k with
  | zero => simp [finiteConjunction, levySyntacticBound]
  | succ k ih =>
    simp only [finiteConjunction, levySyntacticBound]
    exact max_le (hf 0) (ih _ (fun i ↦ hf i.succ))

private theorem bound_standardTuple (n : ℕ) :
    levySyntacticBound (standardTupleValueFormula n) ≤ sparseAtomicSyntaxConstant + 2 * n + 6 := by
  have hn := bound_boundedNumeral n
  have he := bound_finiteConjunction (fun i : Fin n ↦ standardTupleEntryFormula i)
    (fun i ↦ bound_tupleEntry i)
  have hs : levySyntacticBound sequenceSupportFormula ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
  have hf : levySyntacticBound boundedFunctionFormula ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (by simp [sparseAtomicSyntaxDictionary])
  simp only [standardTupleValueFormula, boundedStandardTupleFormula, boundedSetExs,
    levySyntacticBound, levySyntacticBound_rew]
  omega

private theorem atomic_arithmetic (C n N T P M F ep em : ℕ)
    (hN : N ≤ C + 6*n) (hT : T ≤ C + 2*n + 6)
    (hep : ep ≤ n+10) (hem : em ≤ n+10)
    (hP : P ≤ C + 4*ep + 6) (hM : M ≤ C + 4*em + 6) (hF : F ≤ C) :
    max N (max P (max T F)) + 2 + 2 + 2 ≤ C + 6*n + 60 ∧
    max N (max M (max T F)) + 2 + 2 + 2 ≤ C + 6*n + 60 := by
  constructor <;> omega

/-- The raw syntax bound for an atomic forcing clause is linear in its context. -/
theorem sparseBoundedForcingBase_atom_bound {n a} (r : Language.Set.Rel a)
    (ts : Fin a → SetTheorySemiterm Empty n) :
    levySyntacticBound (sparseBoundedForcingBase (.rel r ts)) ≤
      sparseAtomicSyntaxConstant + 6 * n + 60 ∧
    levySyntacticBound (sparseBoundedForcingBase (.nrel r ts)) ≤
      sparseAtomicSyntaxConstant + 6 * n + 60 := by
  have hn := bound_numeral n
  have ht := bound_standardTuple n
  have he := expressionDepth_atom r ts
  have hp := bound_closedExpression (membershipFormulaExpression (.rel r ts))
  have hm := bound_closedExpression (membershipFormulaExpression (.nrel r ts))
  have hf : levySyntacticBound woodinSparseLocalForcingFormula ≤ sparseAtomicSyntaxConstant := by
    exact atomic_graph_bound (φ := woodinSparseLocalForcingFormula)
      (List.getElem_mem (l := sparseAtomicSyntaxDictionary)
      (n := 10) (by decide))
  have h := atomic_arithmetic sparseAtomicSyntaxConstant n
    (levySyntacticBound (numeralFormula n)) (levySyntacticBound (standardTupleValueFormula n))
    (levySyntacticBound (closedCodeExpressionFormula (membershipFormulaExpression (.rel r ts))))
    (levySyntacticBound (closedCodeExpressionFormula (membershipFormulaExpression (.nrel r ts))))
    (levySyntacticBound woodinSparseLocalForcingFormula)
    (expressionDepth (membershipFormulaExpression (.rel r ts)))
    (expressionDepth (membershipFormulaExpression (.nrel r ts))) hn ht he.1 he.2 hp hm hf
  simpa only [sparseBoundedForcingBase, encodeMembershipFormulaFormula,
    BoundedFormulaTree.formula, levySyntacticBound, levySyntacticBound_rew] using h

end ZFVP
