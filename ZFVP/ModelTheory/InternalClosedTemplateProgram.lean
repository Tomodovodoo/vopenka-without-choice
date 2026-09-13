import ZFVP.ModelTheory.InternalClosureProgram

/-! Closed template programs produce well-formed sentences with the expected truth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem prefixSize_zero (m : ℕ) : prefixSize m (0 : V) = (m : V) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [prefixSize, ih, num_succ_def]

theorem prependTuple_zero {m : ℕ} (v : Fin m → V) : prependTuple (0 : V) ∅ v = standardTuple v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [prependTuple, standardTuple, ih, prefixSize_zero]

theorem prefixRenaming_zero {a m : ℕ} (r : Fin a → Fin m) :
    ZFVP.prefixRenaming r (0 : V) = standardTuple (fun i ↦ ((r i).val : V)) := by
  have hskip : skipIndices m (0 : V) = ∅ := by
    apply mem_ext
    intro p
    simp only [skipIndices, mem_definableGraph_iff, zero_def, not_mem_empty, false_and, exists_false]
  rw [ZFVP.prefixRenaming, hskip, prependTuple_zero]

namespace MembershipTemplate

theorem compileTail_zero {a m : ℕ} (t : MembershipTemplate a m) (φ : V) :
    t.compileTail (0 : V) φ = t.compile φ := by
  induction t with
  | fixed ψ => exact renameMembershipFormula_encode_prefix ψ (by simp)
  | hole r => simp only [compileTail, compile, prefixSize_zero, prefixRenaming_zero]
  | conj s t ihs iht => simp only [compileTail, compile, ihs, iht]
  | disj s t ihs iht => simp only [compileTail, compile, ihs, iht]
  | neg s ih => simp only [compileTail, compile, ih, prefixSize_zero]
  | all s ih => simp only [compileTail, compile, ih]
  | exs s ih => simp only [compileTail, compile, ih]

theorem evalSet_closedTailProgram {a : ℕ} (t : MembershipTemplate a 0) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    t.closedTailProgram.evalSet (naturalSquarePair n c) =
      universalClosure.evalSet (naturalSquarePair n (t.compileTailProgram.evalSet (naturalSquarePair n c))) := by
  simp only [closedTailProgram, evalSet_comp, evalSet_pair, evalSet_left,
    naturalSquareLeft, naturalSquareUnpair_pair hn hc]

theorem closedTailProgram_requirementFits {a : ℕ} (t : MembershipTemplate a 0) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    requirementFits ((formulaRequirement false).evalSet (t.closedTailProgram.evalSet (naturalSquarePair n c))) 0 := by
  rw [evalSet_closedTailProgram t hn hc]
  apply requirementFits_universalClosure false hn (by simp) (evalSet_natural _ (naturalSquarePair_natural hn hc))
  rw [ordinalAdd_zero_left_natural hn]
  exact t.compileTailProgram_requirementFits hn hc hv

theorem decodedNaturalFormula_closedTailProgram_valid {a : ℕ} (t : MembershipTemplate a 0) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    decodedNaturalFormula (t.closedTailProgram.evalSet (naturalSquarePair n c)) ∈
      formulaSet (membershipLanguageCode : V) ∅ 0 :=
  decodedNaturalFormula_valid false (evalSet_natural _ (naturalSquarePair_natural hn hc)) (by simp)
    (t.closedTailProgram_requirementFits hn hc hv)

theorem membershipSatisfies_closedTailProgram {a : ℕ} (t : MembershipTemplate a 0) {U n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n))
    (hs : ∀ b ∈ U ^ n, MembershipSatisfies U n (t.compileTail n (decodedNaturalFormula c)) b) :
    MembershipSatisfies U 0 (decodedNaturalFormula (t.closedTailProgram.evalSet (naturalSquarePair n c))) ∅ := by
  rw [evalSet_closedTailProgram t hn hc]
  have hcode := evalSet_natural t.compileTailProgram (naturalSquarePair_natural hn hc)
  have hv' : requirementFits ((formulaRequirement false).evalSet
      (t.compileTailProgram.evalSet (naturalSquarePair n c))) (ordinalAdd 0 n) := by
    rw [ordinalAdd_zero_left_natural hn]
    exact t.compileTailProgram_requirementFits hn hc hv
  have hs' : ∀ b ∈ structureDomain (membershipStructureCode U) ^ ordinalAdd (0 : V) n,
      Satisfies membershipLanguageCode (naturalSyntaxFreeDomain false) (membershipStructureCode U) ∅
        (ordinalAdd 0 n) (decodedNaturalFormula (t.compileTailProgram.evalSet (naturalSquarePair n c))) b := by
    simpa only [ordinalAdd_zero_left_natural hn, membershipStructureCode_domain, MembershipSatisfies, membershipSatisfactionGraph, Satisfies,
      naturalSyntaxFreeDomain, Bool.false_eq_true, ite_false,
      t.decodedNaturalFormula_compileTailProgram hn hc hv] using hs
  exact satisfies_universalClosure false (membershipStructureCode U) ∅ hn (by simp) hcode hv' hs' ∅
    (by apply mem_function.intro <;> simp [zero_def])

theorem decodedNaturalFormula_closedTailProgram_zero {a : ℕ} (t : MembershipTemplate a 0) {c : V}
    (hc : c ∈ (ω : V)) (hv : requirementFits ((formulaRequirement false).evalSet c) (a : V)) :
    decodedNaturalFormula (t.closedTailProgram.evalSet (naturalSquarePair 0 c)) = t.compile (decodedNaturalFormula c) := by
  have h0 : (0 : V) ∈ (ω : V) := by simp
  rw [evalSet_closedTailProgram t h0 hc,
    evalSet_universalClosure_zero (evalSet_natural _ (naturalSquarePair_natural h0 hc)),
    t.decodedNaturalFormula_compileTailProgram h0 hc (by simpa only [prefixSize_zero] using hv),
    compileTail_zero]

end MembershipTemplate
end ZFVP
