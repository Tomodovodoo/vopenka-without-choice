import ZFVP.Syntax.PrimitiveProgramGeneratedStandard
import ZFVP.Syntax.PrimitiveProgramRawFormulas
import ZFVP.Syntax.PrimitiveProgramRawTransform

/-! The standard range of the explicit axiom program is exactly the generated ZF+VP theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

theorem MembershipTemplate.compileTailProgram_raw {a m n c : ℕ} (t : MembershipTemplate a m)
    {φ : SetTheorySemisentence n} (hφ : RawFormulaCode c φ) (k : ℕ) :
    t.compileTailProgram.eval (Nat.pair k c) = t.compileTailProgram.eval (Nat.pair k (Encodable.encode φ)) := by
  induction t with
  | fixed ψ => simp only [MembershipTemplate.compileTailProgram, evalNat_constant]
  | hole r =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_comp, evalNat_pair, evalNat_left,
      evalNat_right, evalNat_zero, Nat.unpair_pair]
    exact hφ.formulaTransform reindexArguments _ 0
  | conj s t ihs iht =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
  | disj s t ihs iht =>
    simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
  | neg s ih => simp only [MembershipTemplate.compileTailProgram, evalNat_comp, ih]
  | all s ih => simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, ih]
  | exs s ih => simp only [MembershipTemplate.compileTailProgram, evalNat_tagged, ih]

theorem MembershipTemplate.closedTailProgram_raw {a n c : ℕ} (t : MembershipTemplate a 0)
    {φ : SetTheorySemisentence n} (hφ : RawFormulaCode c φ) (k : ℕ) :
    t.closedTailProgram.eval (Nat.pair k c) = t.closedTailProgram.eval (Nat.pair k (Encodable.encode φ)) := by
  simp only [MembershipTemplate.closedTailProgram, evalNat_comp, evalNat_pair, evalNat_left,
    Nat.unpair_pair, t.compileTailProgram_raw hφ k]

namespace PrimitiveProgram

theorem templateOptionProgram_some_raw {a k c d : ℕ} (t : MembershipTemplate a 0)
    (h : (templateOptionProgram t).eval (Nat.pair k c) = d + 1) :
    ∃ φ : SetTheorySemisentence (k + a), RawFormulaCode c φ ∧
      d = Encodable.encode (∀¹* t.instantiateTail k φ) := by
  have he := evalArithmetic_templateOptionProgram_some t (k : ℕ) c d
  simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticLE_nat, Arithmetic.natCast_nat] at he
  obtain ⟨hv, hout⟩ := he.mp h
  rw [Nat.add_comm a k, ← evalArithmetic_nat] at hv
  obtain ⟨φ, hφ⟩ := formulaRequirement_raw false (ξ := Empty) (fun _ hf ↦ Bool.noConfusion hf) hv
  refine ⟨φ, hφ, ?_⟩
  rw [t.closedTailProgram_raw hφ k, t.closedTailProgram_encode φ] at hout
  exact hout.symm

theorem templateOptionProgram_zero_some_raw {a c d : ℕ} (t : MembershipTemplate a 0)
    (h : (templateOptionProgram t).eval (Nat.pair 0 c) = d + 1) :
    ∃ φ : SetTheorySemisentence a, RawFormulaCode c φ ∧ d = Encodable.encode (t.instantiate φ) := by
  have he := evalArithmetic_templateOptionProgram_some t (0 : ℕ) c d
  simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticLE_nat, Arithmetic.natCast_nat, Nat.add_zero] at he
  obtain ⟨hv, hout⟩ := he.mp h
  rw [← evalArithmetic_nat] at hv
  obtain ⟨φ, hφ⟩ := formulaRequirement_raw false (ξ := Empty) (fun _ hf ↦ Bool.noConfusion hf) hv
  refine ⟨φ, hφ, ?_⟩
  rw [t.closedTailProgram_raw hφ 0, t.closedTailProgram_zero_encode φ] at hout
  exact hout.symm

set_option maxHeartbeats 800000 in
theorem generatedAxiomProgram_sound_nat {e d : ℕ} (h : generatedAxiomProgram.eval e = d + 1) :
    ∃ φ : SetTheorySentence, d = Encodable.encode φ ∧ φ ∈ generatedZFVPTheory := by
  obtain ⟨tag, tail, rfl⟩ : ∃ tag tail, e = Nat.pair tag tail :=
    ⟨e.unpair.1, e.unpair.2, (Nat.pair_unpair e).symm⟩
  obtain ⟨k, c, rfl⟩ : ∃ k c, tail = Nat.pair k c :=
    ⟨tail.unpair.1, tail.unpair.2, (Nat.pair_unpair tail).symm⟩
  have he := evalArithmetic_generatedAxiomProgram (tag : ℕ) k c
  simp only [arithmeticPair_nat, evalArithmetic_nat] at he
  rw [he] at h
  have hfixed (ψ : SetTheorySentence) (hψ : ψ ∈ fixedZFTheory)
      (he : (Encodable.encode ψ + 1 : ℕ) = d + 1) :
      ∃ φ : SetTheorySentence, d = Encodable.encode φ ∧ φ ∈ generatedZFVPTheory :=
    ⟨ψ, Nat.add_right_cancel he.symm, .fixed hψ⟩
  unfold arithmeticGeneratedAxiomValue at h
  split_ifs at h with h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact hfixed Axiom.empty (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.extentionality (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.pairing (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.union (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.power (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.infinity (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed Axiom.foundation (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · exact hfixed equalityBasisSentence (by simp [fixedZFTheory]) (by simpa only [Arithmetic.natCast_nat] using h)
  · rw [arithmeticPair_nat, evalArithmetic_nat] at h
    obtain ⟨φ, _, hd⟩ := templateOptionProgram_some_raw separationTemplate h
    exact ⟨_, hd, .separation k φ⟩
  · rw [arithmeticPair_nat, evalArithmetic_nat] at h
    obtain ⟨φ, _, hd⟩ := templateOptionProgram_some_raw replacementTemplate h
    exact ⟨_, hd, .replacement k φ⟩
  · rw [arithmeticPair_nat, evalArithmetic_nat] at h
    obtain ⟨φ, _, hd⟩ := templateOptionProgram_zero_some_raw vopenkaTemplate h
    exact ⟨_, hd, .vopenka φ⟩

theorem generatedAxiomCheck_iff_nat (c e : ℕ) :
    generatedAxiomCheck.eval (Nat.pair c e) = 1 ↔
      ∃ φ : SetTheorySentence, c = Encodable.encode φ ∧ generatedAxiomProgram.eval e = Encodable.encode φ + 1 := by
  rw [generatedAxiomCheck_nat]
  constructor
  · intro h
    obtain ⟨φ, hφ, _⟩ := generatedAxiomProgram_sound_nat h
    exact ⟨φ, hφ, by simpa only [← hφ] using h⟩
  · rintro ⟨φ, rfl, hφ⟩
    exact hφ

theorem exists_generatedAxiomCheck_iff (φ : SetTheorySentence) :
    (∃ e : ℕ, generatedAxiomCheck.eval (Nat.pair (Encodable.encode φ) e) = 1) ↔ φ ∈ generatedZFVPTheory := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨ψ, hψ, hm⟩ := generatedAxiomProgram_sound_nat ((generatedAxiomCheck_nat _ _).mp he)
    have heq := Encodable.encode_injective hψ
    exact heq.symm ▸ hm
  · exact generatedAxiomCheck_complete

end PrimitiveProgram
end ZFVP
