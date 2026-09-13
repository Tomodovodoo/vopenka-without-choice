import ZFVP.Syntax.PrimitiveProgramFormulaRequirements
import ZFVP.Syntax.PrimitiveProgramNegationStandard

/-! Well-formed standard membership syntax is accepted with its stated bound-variable context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem arithmeticLE_nat (x y : ℕ) : @LE.le ℕ Arithmetic.instLE_foundation x y ↔ x ≤ y := by
  change x = y ∨ x < y ↔ x ≤ y
  omega

namespace PrimitiveProgram

variable {ξ : Type*} [Encodable ξ]

theorem termRequirement_encode_valid (allowFree : Bool) (hfree : ∀ _ : ξ, allowFree = true)
    {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) :
    (termRequirement allowFree).evalArithmetic (Encodable.encode t : ℕ) ≠ 0 ∧
      (termRequirement allowFree).evalArithmetic (Encodable.encode t : ℕ) ≤ n + 1 := by
  classical
  cases t with
  | bvar i =>
    have he := evalArithmetic_termRequirement_bound allowFree (i.val : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero] at he
    change (termRequirement allowFree).evalArithmetic (Nat.pair 0 i.val + 1) ≠ 0 ∧
      (termRequirement allowFree).evalArithmetic (Nat.pair 0 i.val + 1) ≤ n + 1
    rw [he]
    have := i.isLt
    change i.val + 1 + 1 ≠ 0 ∧ i.val + 1 + 1 ≤ n + 1
    omega
  | fvar x =>
    have he := evalArithmetic_termRequirement_free allowFree (Encodable.encode x : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, hfree x] at he
    change (termRequirement allowFree).evalArithmetic (Nat.pair 1 (Encodable.encode x) + 1) ≠ 0 ∧
      (termRequirement allowFree).evalArithmetic (Nat.pair 1 (Encodable.encode x) + 1) ≤ n + 1
    rw [hfree x, he]
    simp
  | func f _ => exact Empty.elim f

theorem atomicRequirement_encode_valid (allowFree : Bool) (hfree : ∀ _ : ξ, allowFree = true)
    {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ ξ n) :
    let c := Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i))))
    (atomicRequirement allowFree).evalArithmetic c ≠ 0 ∧
      (atomicRequirement allowFree).evalArithmetic c ≤ n + 1 := by
  classical
  dsimp only
  have he := evalArithmetic_atomicRequirement allowFree (k : ℕ) (Encodable.encode r : ℕ)
    (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))
  simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat] at he
  rw [he]
  cases r
  all_goals
    have hv : Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)) =
        Encodable.encode [Encodable.encode (ts 0), Encodable.encode (ts 1)] := rfl
    have hl := evalArithmetic_listLength_encode [Encodable.encode (ts 0), Encodable.encode (ts 1)]
    rw [← hv] at hl
    simp only [List.length_cons, List.length_nil] at hl
    simp only [show Encodable.encode Language.Set.Rel.eq = 0 from rfl,
      show Encodable.encode Language.Set.Rel.mem = 1 from rfl]
    simp only [hl, ite_true, arithmeticLE_nat]
    norm_num only
    have ha := termRequirement_encode_valid allowFree hfree (ts 0)
    have hb := termRequirement_encode_valid allowFree hfree (ts 1)
    have hheads : Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)) =
        Nat.pair (Encodable.encode (ts 0)) (Nat.pair (Encodable.encode (ts 1)) 0 + 1) + 1 := rfl
    simp only [hheads, ← arithmeticPair_nat, evalArithmetic_listHead_cons, evalArithmetic_listTail_cons]
    have hj := joinRequirements_valid_iff (M := ℕ)
      ((termRequirement allowFree).evalArithmetic (Encodable.encode (ts 0)))
      ((termRequirement allowFree).evalArithmetic (Encodable.encode (ts 1))) (n + 1)
    simp only [arithmeticLE_nat] at hj
    exact hj.mpr ⟨ha, hb⟩

theorem formulaRequirement_encode_valid (allowFree : Bool) (hfree : ∀ _ : ξ, allowFree = true)
    {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    (formulaRequirement allowFree).evalArithmetic (Encodable.encode φ : ℕ) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Encodable.encode φ : ℕ) ≤ n + 1 := by
  induction φ with
  | verum =>
    have he := evalArithmetic_formulaRequirement_verum allowFree (0 : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 2 0 + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 2 0 + 1) ≤ _
    rw [he]
    simp
  | falsum =>
    have he := evalArithmetic_formulaRequirement_falsum allowFree (0 : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 3 0 + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 3 0 + 1) ≤ _
    rw [he]
    simp
  | @rel n k r ts =>
    have he := evalArithmetic_formulaRequirement_rel allowFree
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero] at he
    rw [Semiformula.encode_rel, he]
    exact atomicRequirement_encode_valid allowFree hfree r ts
  | @nrel n k r ts =>
    have he := evalArithmetic_formulaRequirement_nrel allowFree
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one] at he
    rw [Semiformula.encode_nrel, he]
    exact atomicRequirement_encode_valid allowFree hfree r ts
  | @and n φ ψ ihφ ihψ =>
    have he := evalArithmetic_formulaRequirement_and allowFree (Encodable.encode φ : ℕ) (Encodable.encode ψ : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) ≤ _
    rw [he]
    have hj := joinRequirements_valid_iff (M := ℕ)
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode φ))
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode ψ)) (n + 1)
    simp only [arithmeticLE_nat, arithmeticPair_nat] at hj
    exact hj.mpr ⟨ihφ, ihψ⟩
  | @or n φ ψ ihφ ihψ =>
    have he := evalArithmetic_formulaRequirement_or allowFree (Encodable.encode φ : ℕ) (Encodable.encode ψ : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) ≤ _
    rw [he]
    have hj := joinRequirements_valid_iff (M := ℕ)
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode φ))
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode ψ)) (n + 1)
    simp only [arithmeticLE_nat, arithmeticPair_nat] at hj
    exact hj.mpr ⟨ihφ, ihψ⟩
  | @all n φ ih =>
    have he := evalArithmetic_formulaRequirement_all allowFree (Encodable.encode φ : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 6 (Encodable.encode φ) + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 6 (Encodable.encode φ) + 1) ≤ _
    rw [he]
    have hq := quantifyRequirement_valid_iff (M := ℕ)
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode φ)) n
    simp only [arithmeticLE_nat, OfNat.ofNat, One.one, Zero.zero] at hq
    exact hq.mpr ih
  | @exs n φ ih =>
    have he := evalArithmetic_formulaRequirement_exs allowFree (Encodable.encode φ : ℕ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaRequirement allowFree).evalArithmetic (Nat.pair 7 (Encodable.encode φ) + 1) ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic (Nat.pair 7 (Encodable.encode φ) + 1) ≤ _
    rw [he]
    have hq := quantifyRequirement_valid_iff (M := ℕ)
      ((formulaRequirement allowFree).evalArithmetic (Encodable.encode φ)) n
    simp only [arithmeticLE_nat, OfNat.ofNat, One.one, Zero.zero] at hq
    exact hq.mpr ih

theorem formulaRequirement_sentence (φ : SetTheorySentence) :
    (formulaRequirement false).eval (Encodable.encode φ) = 1 := by
  have h := formulaRequirement_encode_valid false (fun x : Empty ↦ Empty.elim x) φ
  rw [evalArithmetic_nat] at h
  omega

end PrimitiveProgram
end ZFVP
