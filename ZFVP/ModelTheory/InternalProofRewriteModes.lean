import ZFVP.ModelTheory.InternalProofRewriteSubstitution
import ZFVP.Syntax.PrimitiveProgramProofRewriteModes

/-! Concrete initial variable tables of the three proof-rule rewrite modes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem evalSet_proofRewriteFreshIndex_one : proofRewriteFreshIndex.evalSet (1 : V) = 0 := by
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteFreshIndex_one (M := InternalArithmetic V))
  simpa only [evalArithmetic_agreement, internalArithmeticVal_one, internalArithmeticVal_zero] using h

@[simp] theorem evalSet_proofRewriteFreshIndex_witness {k : V} (hk : k ∈ (ω : V)) :
    proofRewriteFreshIndex.evalSet (SetTheory.succ (SetTheory.succ k)) = k := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteFreshIndex_witness u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ] using h

@[simp] theorem evalSet_proofRewriteFreeIndex_zero {i : V} (hi : i ∈ (ω : V)) :
    proofRewriteFreeIndex.evalSet (naturalSquarePair 0 i) = SetTheory.succ i := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteFreeIndex_zero u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] using h

@[simp] theorem evalSet_proofRewriteFreeIndex_one {i : V} (hi : i ∈ (ω : V)) :
    proofRewriteFreeIndex.evalSet (naturalSquarePair 1 i) = SetTheory.succ i := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteFreeIndex_one u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_one] using h

@[simp] theorem evalSet_proofRewriteFreeIndex_witness {k i : V} (hk : k ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    proofRewriteFreeIndex.evalSet (naturalSquarePair (SetTheory.succ (SetTheory.succ k)) i) = i := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteFreeIndex_witness u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] using h

@[simp] theorem proofRewriteSource_zeroMode (d : V) : proofRewriteSource 0 d = d := by
  simp [proofRewriteSource]

@[simp] theorem proofRewriteSource_oneMode (d : V) : proofRewriteSource 1 d = SetTheory.succ d := by
  simp [proofRewriteSource]

theorem internalSucc_ne_zero (i : V) : SetTheory.succ i ≠ (0 : V) := by
  intro he
  exact not_mem_empty (he ▸ mem_succ_self i)

@[simp] theorem proofRewriteSource_witnessMode (k d : V) :
    proofRewriteSource (SetTheory.succ (SetTheory.succ k)) d = SetTheory.succ d := by
  simp only [proofRewriteSource, internalSucc_ne_zero, ite_false]

@[simp] theorem proofRewriteBoundTable_zeroMode : proofRewriteBoundTable (0 : V) 0 = ∅ := by
  apply SetTheory.mem_ext
  intro p
  simp [proofRewriteBoundTable, mem_definableGraph_iff, proofRewriteSource, zero_def]

theorem proofRewriteBoundTable_open_value {s : V} (hs : s ∈ (ω : V)) (hs0 : s ≠ 0) :
    (proofRewriteBoundTable s 0) ‘ (0 : V) = freeVarCode (proofRewriteFreshIndex.evalSet s) := by
  have hi : (0 : V) ∈ proofRewriteSource s 0 := by
    simp only [proofRewriteSource, hs0, ite_false, mem_succ_self]
  rw [proofRewriteBoundTable_value hi, naturalProofRewriteTerm_bound_edge hs (by simp [zero_def]) hs0]

theorem proofRewriteFreeTable_zeroMode_value {i : V} (hi : i ∈ (ω : V)) :
    (proofRewriteVariableTable 0 0 1) ‘ i = freeVarCode (SetTheory.succ i) := by
  rw [proofRewriteVariableTable_value _ _ _ hi, naturalProofRewriteTerm_free (by simp [zero_def]) (by simp [zero_def]) hi,
    evalSet_proofRewriteFreeIndex_zero hi]

theorem proofRewriteFreeTable_oneMode_value {i : V} (hi : i ∈ (ω : V)) :
    (proofRewriteVariableTable 1 0 1) ‘ i = freeVarCode (SetTheory.succ i) := by
  rw [proofRewriteVariableTable_value _ _ _ hi, naturalProofRewriteTerm_free (by simp) (by simp [zero_def]) hi,
    evalSet_proofRewriteFreeIndex_one hi]

theorem proofRewriteFreeTable_witnessMode_value {k i : V} (hk : k ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    (proofRewriteVariableTable (SetTheory.succ (SetTheory.succ k)) 0 1) ‘ i = freeVarCode i := by
  rw [proofRewriteVariableTable_value _ _ _ hi,
    naturalProofRewriteTerm_free (ω_succ_closed (ω_succ_closed hk)) (by simp [zero_def]) hi,
    evalSet_proofRewriteFreeIndex_witness hk hi]

theorem proofRewriteFreeTable_eigen_eq_shift :
    proofRewriteVariableTable (1 : V) 0 1 = proofRewriteVariableTable 0 0 1 := by
  apply function_eq_of_values (proofRewriteFreeTable_mem (by simp) (by simp [zero_def]))
    (proofRewriteFreeTable_mem (by simp [zero_def]) (by simp [zero_def]))
  intro i hi
  rw [proofRewriteFreeTable_oneMode_value hi, proofRewriteFreeTable_zeroMode_value hi]

theorem proofRewriteFreeTable_witness_eq_identity {k : V} (hk : k ∈ (ω : V)) :
    proofRewriteVariableTable (SetTheory.succ (SetTheory.succ k)) 0 1 = freeIdentityReplacement (ω : V) := by
  apply function_eq_of_values (proofRewriteFreeTable_mem (ω_succ_closed (ω_succ_closed hk)) (by simp [zero_def]))
    (freeIdentityReplacement_mem membershipLanguageCode_valid (by simp [zero_def]) _)
  intro i hi
  rw [proofRewriteFreeTable_witnessMode_value hk hi, freeIdentityReplacement_value hi]

end ZFVP
