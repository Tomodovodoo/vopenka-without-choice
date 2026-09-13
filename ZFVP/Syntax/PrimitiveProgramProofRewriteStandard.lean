import ZFVP.Syntax.PrimitiveProgramProofRewriteEquations
import ZFVP.Syntax.PrimitiveProgramRequirementsStandard
import ZFVP.Syntax.NaturalProofRewriting

/-! Standard-natural-number correspondence for the explicit proof-rewriting primitives. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem arithmeticSub_nat (x y : ℕ) : Arithmetic.sub x y = x - y := by
  symm
  apply Arithmetic.sub_eq_iff.mpr
  constructor
  · intro h
    have h' : y ≤ x := (arithmeticLE_nat y x).mp h
    clear h
    change x = y + (x - y)
    omega
  · intro h
    change x < y at h
    change x - y = 0
    omega

theorem arithmeticSubNotation_nat (x y : ℕ) :
    @HSub.hSub ℕ ℕ ℕ (@instHSub ℕ Arithmetic.instSub_foundation) x y = x - y :=
  arithmeticSub_nat x y

theorem arithmeticPiOne_nat (x : ℕ) : Arithmetic.pi₁ x = (Nat.unpair x).1 := by
  simp [Arithmetic.pi₁, arithmeticUnpair_nat]

theorem arithmeticPiTwo_nat (x : ℕ) : Arithmetic.pi₂ x = (Nat.unpair x).2 := by
  simp [Arithmetic.pi₂, arithmeticUnpair_nat]

namespace PrimitiveProgram

theorem arithmeticProofRewriteTerm_nat (s d c : ℕ) :
    arithmeticProofRewriteTerm s d c = proofRewNatTerm s d c := by
  classical
  unfold arithmeticProofRewriteTerm proofRewNatTerm
  simp only [OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, arithmeticSubNotation_nat,
    arithmeticPiOne_nat, arithmeticPiTwo_nat, arithmeticPair_nat]

theorem proofRewriteTerm_nat (s d c : ℕ) :
    proofRewriteTerm.eval (Nat.pair s (Nat.pair d c)) = proofRewNatTerm s d c := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, ← arithmeticPair_nat,
    evalArithmetic_proofRewriteTerm, arithmeticProofRewriteTerm_nat]

theorem proofRewriteArguments_nat (s d c : ℕ) :
    proofRewriteArguments.eval (Nat.pair s (Nat.pair d c)) = proofRewNatArguments s d c := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, ← arithmeticPair_nat, evalArithmetic_proofRewriteArguments]
  unfold proofRewNatArguments natVectorTwo
  simp only [evalArithmetic_listHead, evalArithmetic_listTail, OfNat.ofNat, One.one, Zero.zero,
    arithmeticSubNotation_nat, arithmeticPiOne_nat, arithmeticPiTwo_nat, arithmeticPair_nat,
    arithmeticProofRewriteTerm_nat]

theorem proofRewriteCode_encode (s d : ℕ) {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) :
    proofRewriteCode.eval (Nat.pair s (Nat.pair d (Encodable.encode φ))) =
      proofRewNatFormula s d (Encodable.encode φ) := by
  induction φ generalizing d with
  | verum =>
    have he := evalArithmetic_proofRewriteCode_verum (M := ℕ) s d 0
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 2 0 + 1))) = _
    rw [he]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]
  | falsum =>
    have he := evalArithmetic_proofRewriteCode_falsum (M := ℕ) s d 0
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 3 0 + 1))) = _
    rw [he]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]
  | @rel n k r ts =>
    have he := evalArithmetic_proofRewriteCode_rel (M := ℕ) s d
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat,
      arithmeticPiOne_nat, arithmeticPiTwo_nat, Nat.unpair_pair, evalArithmetic_nat, proofRewriteArguments_nat] at he
    rw [Semiformula.encode_rel, he]
    cases r <;> simp [proofRewNatFormula]
  | @nrel n k r ts =>
    have he := evalArithmetic_proofRewriteCode_nrel (M := ℕ) s d
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat,
      arithmeticPiOne_nat, arithmeticPiTwo_nat, Nat.unpair_pair, evalArithmetic_nat, proofRewriteArguments_nat] at he
    rw [Semiformula.encode_nrel, he]
    cases r <;> simp [proofRewNatFormula]
  | and φ ψ ihφ ihψ =>
    have he := evalArithmetic_proofRewriteCode_and (M := ℕ) s d (Encodable.encode φ) (Encodable.encode ψ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1))) = _
    rw [he, ihφ, ihψ]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]
  | or φ ψ ihφ ihψ =>
    have he := evalArithmetic_proofRewriteCode_or (M := ℕ) s d (Encodable.encode φ) (Encodable.encode ψ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1))) = _
    rw [he, ihφ, ihψ]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]
  | all φ ih =>
    have he := evalArithmetic_proofRewriteCode_all (M := ℕ) s d (Encodable.encode φ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 6 (Encodable.encode φ) + 1))) = _
    rw [he, ih]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]
  | exs φ ih =>
    have he := evalArithmetic_proofRewriteCode_exs (M := ℕ) s d (Encodable.encode φ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change proofRewriteCode.eval (Nat.pair s (Nat.pair d (Nat.pair 7 (Encodable.encode φ) + 1))) = _
    rw [he, ih]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, proofRewNatFormula]

theorem proofRewriteCode_rew_encode (s d : ℕ) {n m : ℕ} (σ : Rew ℒₛₑₜ ℕ n ℕ m)
    (hσ : ∀ t, proofRewNatTerm s d (Encodable.encode t) = Encodable.encode (σ t))
    (φ : Semiproposition ℒₛₑₜ n) :
    proofRewriteCode.eval (Nat.pair s (Nat.pair d (Encodable.encode φ))) = Encodable.encode (σ ▹ φ) := by
  rw [proofRewriteCode_encode, proofRewNatFormula_encode s d σ hσ]
end PrimitiveProgram
end ZFVP
