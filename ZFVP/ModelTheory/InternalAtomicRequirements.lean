import ZFVP.ModelTheory.InternalTermRequirements

/-! Accepted internal atomic codes decode to well-formed membership atoms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem decodedNaturalAtomic_valid (allowFree : Bool) {k r args n : V}
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (ha : args ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet
      (naturalSquarePair k (naturalSquarePair r args))) n) :
    IsAtomicArguments membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n
      (relationToken r) (decodedNaturalArguments args) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨z, rfl⟩ := internalArithmeticVal_surjective hn
  simp only [← internalArithmeticVal_pair, ← evalArithmetic_agreement, requirementFits_val,
    atomicRequirement_valid_iff] at hv
  have hv0 : requirementFits ((termRequirement allowFree).evalSet (listHead.evalSet (internalArithmeticVal w)))
      (internalArithmeticVal z) := by
    simpa only [← evalArithmetic_agreement, requirementFits_val] using hv.2.2.2.1
  have hv1 : requirementFits ((termRequirement allowFree).evalSet
      (listHead.evalSet (listTail.evalSet (internalArithmeticVal w)))) (internalArithmeticVal z) := by
    simpa only [← evalArithmetic_agreement, requirementFits_val] using hv.2.2.2.2
  have ht0 := decodedNaturalTerm_valid allowFree (evalSet_natural listHead ha) hn hv0
  have ht1 := decodedNaturalTerm_valid allowFree
    (evalSet_natural listHead (evalSet_natural listTail ha)) hn hv1
  have hsym : internalArithmeticVal v ∈ (2 : V) := by
    change internalArithmeticVal v ∈ SetTheory.succ (1 : V)
    rw [← internalArithmeticVal_one, ← internalArithmeticVal_succ, ← internalArithmetic_lt]
    exact lt_succ_iff_le.mpr hv.2.1
  have har : (relationArities (membershipLanguageCode : V)) ‘ (internalArithmeticVal v) = (2 : V) := by
    simp only [membershipLanguageCode, relationArities_code]
    exact value_constantGraph _ _ hsym
  refine Or.inr ⟨internalArithmeticVal v, ?_, rfl, ?_⟩
  · simpa only [membershipLanguageCode, relationSymbols_code] using hsym
  · rw [har]
    unfold decodedNaturalArguments
    apply standardTuple_mem_function
    intro i
    fin_cases i
    · exact ht0
    · exact ht1

end ZFVP