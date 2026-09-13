import ZFVP.ModelTheory.InternalTemplateFixed
import ZFVP.ModelTheory.InternalReindexRequirements
import ZFVP.ModelTheory.InternalRequirementConstructors
import ZFVP.ModelTheory.InternalNegationProgram

/-! The explicit template compiler agrees with internal parameter-tail compilation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_tagged (k : ℕ) (p : PrimitiveProgram) (x : V) :
    (tagged k p).evalSet x = succ (naturalSquarePair (SetTheory.ofNat k : V) (p.evalSet x)) := by
  simp only [tagged, evalSet_comp, evalSet_succ, evalSet_pair, evalSet_constant, setNatCast_eq_ofNat]

namespace MembershipTemplate

theorem compileTailProgram_requirementFits {a m : ℕ} (t : MembershipTemplate a m) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    requirementFits ((formulaRequirement false).evalSet (t.compileTailProgram.evalSet (naturalSquarePair n c)))
      (prefixSize m n) := by
  have hin := naturalSquarePair_natural hn hc
  induction t with
  | fixed ψ =>
    rw [compileTailProgram, evalSet_constant]
    exact requirementFits_encode_prefix ψ hn
  | hole r =>
    simp only [compileTailProgram, evalSet_comp, evalSet_pair, evalSet_zero, evalSet_left, evalSet_right,
      naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair hn hc]
    exact requirementFits_prefixProgram r hn hc hv
  | conj s t ihs iht =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 4 : V) = (4 : V) from rfl, evalSet_pair, requirementFits_formula_and false
      (evalSet_natural _ hin) (evalSet_natural _ hin) (prefixSize_natural _ hn)]
    exact ⟨ihs, iht⟩
  | disj s t ihs iht =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 5 : V) = (5 : V) from rfl, evalSet_pair, requirementFits_formula_or false
      (evalSet_natural _ hin) (evalSet_natural _ hin) (prefixSize_natural _ hn)]
    exact ⟨ihs, iht⟩
  | neg s ih =>
    rw [compileTailProgram, evalSet_comp, requirementFits_negateCode false (evalSet_natural _ hin)]
    exact ih
  | all s ih =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 6 : V) = (6 : V) from rfl,
      requirementFits_formula_all false (evalSet_natural _ hin) (prefixSize_natural _ hn)]
    exact ih
  | exs s ih =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 7 : V) = (7 : V) from rfl,
      requirementFits_formula_exs false (evalSet_natural _ hin) (prefixSize_natural _ hn)]
    exact ih

theorem decodedNaturalFormula_compileTailProgram {a m : ℕ} (t : MembershipTemplate a m) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    decodedNaturalFormula (t.compileTailProgram.evalSet (naturalSquarePair n c)) =
      t.compileTail n (decodedNaturalFormula c) := by
  have hin := naturalSquarePair_natural hn hc
  induction t with
  | fixed ψ =>
    rw [compileTailProgram, evalSet_constant, decodedNaturalFormula_membership, compileTail,
      renameMembershipFormula_encode_prefix ψ hn]
  | hole r =>
    simp only [compileTailProgram, evalSet_comp, evalSet_pair, evalSet_zero, evalSet_left, evalSet_right,
      naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair hn hc]
    exact decodedNaturalFormula_prefixProgram r hn hc hv
  | conj s t ihs iht =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 4 : V) = (4 : V) from rfl, evalSet_pair,
      decodedNaturalFormula_and (evalSet_natural _ hin) (evalSet_natural _ hin), ihs, iht]
    rfl
  | disj s t ihs iht =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 5 : V) = (5 : V) from rfl, evalSet_pair,
      decodedNaturalFormula_or (evalSet_natural _ hin) (evalSet_natural _ hin), ihs, iht]
    rfl
  | neg s ih =>
    rw [compileTailProgram, evalSet_comp, decodedNaturalFormula_negateCode false
      (evalSet_natural _ hin) (prefixSize_natural _ hn) (s.compileTailProgram_requirementFits hn hc hv), ih]
    rfl
  | all s ih =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 6 : V) = (6 : V) from rfl, decodedNaturalFormula_all (evalSet_natural _ hin), ih]
    rfl
  | exs s ih =>
    rw [compileTailProgram, evalSet_tagged, show (SetTheory.ofNat 7 : V) = (7 : V) from rfl, decodedNaturalFormula_exs (evalSet_natural _ hin), ih]
    rfl

theorem decodedNaturalFormula_compileTailProgram_valid {a m : ℕ} (t : MembershipTemplate a m) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    decodedNaturalFormula (t.compileTailProgram.evalSet (naturalSquarePair n c)) ∈
      formulaSet membershipLanguageCode ∅ (prefixSize m n) :=
  decodedNaturalFormula_valid false (evalSet_natural _ (naturalSquarePair_natural hn hc))
    (prefixSize_natural m hn) (t.compileTailProgram_requirementFits hn hc hv)

end MembershipTemplate
end ZFVP
