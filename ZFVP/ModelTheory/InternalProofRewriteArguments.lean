import ZFVP.ModelTheory.InternalProofRewriteTables

/-! Rewriting binary atomic argument vectors agrees with internal term substitution. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_proofRewriteArguments {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    proofRewriteArguments.evalSet (naturalSquarePair s (naturalSquarePair d c)) =
      SetTheory.succ (naturalSquarePair
        (proofRewriteTerm.evalSet (naturalSquarePair s (naturalSquarePair d (listHead.evalSet c))))
        (SetTheory.succ (naturalSquarePair
          (proofRewriteTerm.evalSet (naturalSquarePair s
            (naturalSquarePair d (listHead.evalSet (listTail.evalSet c))))) 0))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteArguments u v w)
  simp only [← evalArithmetic_proofRewriteTerm] at h
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ,
    internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem decodedNaturalArguments_two {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    decodedNaturalArguments (SetTheory.succ (naturalSquarePair a
      (SetTheory.succ (naturalSquarePair b 0)))) =
      standardTuple ![decodedNaturalTerm a, decodedNaturalTerm b] := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have ht := ω_succ_closed (naturalSquarePair_natural hb h0)
  simp only [decodedNaturalArguments, evalSet_listHead_cons ha ht, evalSet_listTail_cons ha ht,
    evalSet_listHead_cons hb h0]

theorem decodedNaturalArguments_proofRewrite {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    decodedNaturalArguments (proofRewriteArguments.evalSet (naturalSquarePair s (naturalSquarePair d c))) =
      standardTuple ![naturalProofRewriteTerm s d (listHead.evalSet c),
        naturalProofRewriteTerm s d (listHead.evalSet (listTail.evalSet c))] := by
  rw [evalSet_proofRewriteArguments hs hd hc,
    decodedNaturalArguments_two
      (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural hd (evalSet_natural _ hc))))
      (evalSet_natural _ (naturalSquarePair_natural hs
        (naturalSquarePair_natural hd (evalSet_natural _ (evalSet_natural _ hc)))))]
  rfl

theorem atomicRequirement_term_fits (allowFree : Bool) {k r c n : V}
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    requirementFits ((termRequirement allowFree).evalSet (listHead.evalSet c)) n ∧
      requirementFits ((termRequirement allowFree).evalSet (listHead.evalSet (listTail.evalSet c))) n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨z, rfl⟩ := internalArithmeticVal_surjective hn
  simp only [← internalArithmeticVal_pair, ← evalArithmetic_agreement, requirementFits_val,
    atomicRequirement_valid_iff] at hv
  simpa only [← evalArithmetic_agreement, requirementFits_val] using hv.2.2.2

theorem decodedNaturalArguments_proofRewrite_substitution (allowFree : Bool) {s d k r c n : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    decodedNaturalArguments (proofRewriteArguments.evalSet (naturalSquarePair s (naturalSquarePair d c))) =
      compose (decodedNaturalArguments c)
        (termSubstitution membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n
          (proofRewriteVariableTable s d 0) (proofRewriteVariableTable s d 1)) := by
  have hv' := atomicRequirement_term_fits allowFree hk hr hc hn hv
  have ha := evalSet_natural listHead hc
  have hb := evalSet_natural listHead (evalSet_natural listTail hc)
  rw [decodedNaturalArguments_proofRewrite hs hd hc]
  unfold decodedNaturalArguments
  rw [compose_standardTuple _ _ (fun i ↦ by
    rw [domain_termSubstitution]
    fin_cases i
    · exact decodedNaturalTerm_valid allowFree ha hn hv'.1
    · exact decodedNaturalTerm_valid allowFree hb hn hv'.2)]
  apply congrArg standardTuple
  funext i
  fin_cases i
  · exact naturalProofRewriteTerm_substitution allowFree s d ha hn hv'.1
  · exact naturalProofRewriteTerm_substitution allowFree s d hb hn hv'.2

end ZFVP
