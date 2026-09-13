import ZFVP.Syntax.PrimitiveProgramGeneratedAxioms
import ZFVP.Syntax.PrimitiveProgramLKStandardInputs

/-! Every standard axiom of the generated theory has an accepted explicit program witness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

theorem MembershipTemplate.compileTailProgram_zero_encode {a m : ℕ} (t : MembershipTemplate a m)
    (φ : SetTheorySemisentence a) :
    t.compileTailProgram.eval (Nat.pair 0 (Encodable.encode φ)) = Encodable.encode (t.instantiate φ) := by
  induction t with
  | fixed ψ => exact evalNat_constant _ _
  | hole r =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_comp, evalNat_pair, evalNat_left,
      evalNat_right, evalNat_zero, Nat.unpair_pair, prefixRenaming_nat, natPrefixRenaming,
      List.range_zero, List.map_nil, List.append_nil]
    exact reindexCode_boundIndexRew_encode r φ
  | conj s t ihs iht =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
    rfl
  | disj s t ihs iht =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
    rfl
  | neg s ih =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_comp, ih, negateCode_encode]
    rfl
  | all s ih =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, ih]
    rfl
  | exs s ih =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, ih]
    rfl

theorem MembershipTemplate.closedTailProgram_zero_encode {a : ℕ} (t : MembershipTemplate a 0)
    (φ : SetTheorySemisentence a) :
    t.closedTailProgram.eval (Nat.pair 0 (Encodable.encode φ)) = Encodable.encode (t.instantiate φ) := by
  simp only [MembershipTemplate.closedTailProgram, evalNat_comp, evalNat_pair, evalNat_left,
    Nat.unpair_pair, t.compileTailProgram_zero_encode φ]
  have h := evalArithmetic_universalClosure_zero (Encodable.encode (t.instantiate φ) : ℕ)
  simpa only [arithmeticPair_nat, evalArithmetic_nat] using h

namespace PrimitiveProgram

theorem templateOptionProgram_encode {a k : ℕ} (t : MembershipTemplate a 0)
    (φ : SetTheorySemisentence (k + a)) :
    (templateOptionProgram t).eval (Nat.pair k (Encodable.encode φ)) =
      Encodable.encode (∀¹* t.instantiateTail k φ) + 1 := by
  have h := evalArithmetic_templateOptionProgram t (k : ℕ) (Encodable.encode φ : ℕ)
  simp only [arithmeticPair_nat, evalArithmetic_nat, Arithmetic.natCast_nat] at h
  rw [Nat.add_comm a k, formulaCheck_encode false Empty.elim φ] at h
  simpa only [Nat.one_ne_zero, ite_false, t.closedTailProgram_encode φ] using h

theorem templateOptionProgram_zero_encode {a : ℕ} (t : MembershipTemplate a 0)
    (φ : SetTheorySemisentence a) :
    (templateOptionProgram t).eval (Nat.pair 0 (Encodable.encode φ)) =
      Encodable.encode (t.instantiate φ) + 1 := by
  have h := evalArithmetic_templateOptionProgram t (0 : ℕ) (Encodable.encode φ : ℕ)
  simp only [arithmeticPair_nat, evalArithmetic_nat, Arithmetic.natCast_nat, Nat.add_zero] at h
  rw [formulaCheck_encode false Empty.elim φ] at h
  simpa only [Nat.one_ne_zero, ite_false, t.closedTailProgram_zero_encode φ] using h

theorem generatedAxiomCheck_nat (φ e : ℕ) :
    generatedAxiomCheck.eval (Nat.pair φ e) = 1 ↔ generatedAxiomProgram.eval e = φ + 1 := by
  simpa only [arithmeticPair_nat, evalArithmetic_nat] using evalArithmetic_generatedAxiomCheck φ e

theorem generatedAxiomProgram_complete {φ : SetTheorySentence} (hφ : φ ∈ generatedZFVPTheory) :
    ∃ e : ℕ, generatedAxiomProgram.eval e = Encodable.encode φ + 1 := by
  have hgen (tag k c : ℕ) := evalArithmetic_generatedAxiomProgram tag k c
  simp only [arithmeticPair_nat, evalArithmetic_nat] at hgen
  cases hφ with
  | fixed h =>
    simp only [fixedZFTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Nat.pair 0 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 1 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 2 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 3 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 4 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 5 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 6 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
    · exact ⟨Nat.pair 7 (Nat.pair 0 0), by rw [hgen]; simp [arithmeticGeneratedAxiomValue]⟩
  | separation k φ =>
    refine ⟨Nat.pair 8 (Nat.pair k (Encodable.encode φ)), ?_⟩
    rw [hgen]
    simp [arithmeticGeneratedAxiomValue]
    rw [arithmeticPair_nat, evalArithmetic_nat]
    exact templateOptionProgram_encode separationTemplate φ
  | replacement k φ =>
    refine ⟨Nat.pair 9 (Nat.pair k (Encodable.encode φ)), ?_⟩
    rw [hgen]
    simp [arithmeticGeneratedAxiomValue]
    rw [arithmeticPair_nat, evalArithmetic_nat]
    exact templateOptionProgram_encode replacementTemplate φ
  | vopenka φ =>
    refine ⟨Nat.pair 10 (Nat.pair 0 (Encodable.encode φ)), ?_⟩
    rw [hgen]
    simp [arithmeticGeneratedAxiomValue]
    rw [arithmeticPair_nat, evalArithmetic_nat]
    exact templateOptionProgram_zero_encode vopenkaTemplate φ

theorem generatedAxiomCheck_complete {φ : SetTheorySentence} (hφ : φ ∈ generatedZFVPTheory) :
    ∃ e : ℕ, generatedAxiomCheck.eval (Nat.pair (Encodable.encode φ) e) = 1 := by
  simpa only [generatedAxiomCheck_nat] using generatedAxiomProgram_complete hφ

end PrimitiveProgram
end ZFVP
