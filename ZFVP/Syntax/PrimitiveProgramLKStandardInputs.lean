import ZFVP.Syntax.PrimitiveProgramListStandard
import ZFVP.Syntax.NaturalLKRule

/-! Standard LK witnesses pass the explicit input checks and use the encoded Foundation rewrites. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem formulaCheck_encode {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hfree : ∀ _ : ξ, allowFree = true) {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    (formulaCheck allowFree).eval (Nat.pair n (Encodable.encode φ)) = 1 := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_formulaCheck_eq_one, arithmeticLE_nat]
  exact formulaRequirement_encode_valid allowFree hfree φ

theorem sequentCheck_encode {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hfree : ∀ _ : ξ, allowFree = true) {n : ℕ} (Γ : List (Semiformula ℒₛₑₜ ξ n)) :
    (sequentCheck allowFree).eval (Nat.pair n (Encodable.encode Γ)) = 1 := by
  rw [sequentCheck, listAll_encode_iff]
  intro φ _
  rw [formulaCheck_encode allowFree hfree φ]
  decide

theorem arithmeticLKInputs_encode (S : List (Sequent ℒₛₑₜ)) (C : Sequent ℒₛₑₜ)
    (φ ψ : SetTheoryProposition) (θ : Semiproposition ℒₛₑₜ 1) (Γ Δ : Sequent ℒₛₑₜ) :
    arithmeticLKInputs (Encodable.encode S : ℕ) (Encodable.encode C : ℕ)
      (Encodable.encode φ : ℕ) (Encodable.encode ψ : ℕ) (Encodable.encode θ : ℕ)
      (Encodable.encode Γ : ℕ) (Encodable.encode Δ : ℕ) := by
  have hS' : ∀ i < listLength.evalArithmetic (Encodable.encode S : ℕ),
      (sequentCheck true).evalArithmetic (Arithmetic.pair 0
        (listGet.evalArithmetic (Arithmetic.pair (Encodable.encode S) i))) = 1 := by
    rw [← encode_list_map_encode S, evalArithmetic_listLength_encode]
    intro i hi
    rw [evalArithmetic_listGet_encode _ i hi]
    obtain ⟨xs, _, he⟩ := List.mem_map.mp (List.getElem_mem hi)
    rw [← he, arithmeticPair_nat, evalArithmetic_nat]
    exact sequentCheck_encode true (fun _ ↦ rfl) xs
  unfold arithmeticLKInputs
  refine ⟨?_, hS', ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [arithmeticPair_nat, evalArithmetic_nat]
  · exact sequentCheck_encode true (fun _ ↦ rfl) C
  · exact formulaCheck_encode true (fun _ ↦ rfl) φ
  · exact formulaCheck_encode true (fun _ ↦ rfl) ψ
  · exact formulaCheck_encode true (fun _ ↦ rfl) θ
  · exact sequentCheck_encode true (fun _ ↦ rfl) Γ
  · exact sequentCheck_encode true (fun _ ↦ rfl) Δ

theorem proofRewriteAtZero_shift_encode (φ : SetTheoryProposition) :
    proofRewriteAtZero.eval (Nat.pair 0 (Encodable.encode φ)) = Encodable.encode φ.shift := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_proofRewriteAtZero]
  simp only [arithmeticPair_nat, evalArithmetic_nat]
  rw [proofRewriteCode_encode, proofRewNatFormula_shift]

theorem proofRewriteAtZero_free_encode (φ : Semiproposition ℒₛₑₜ 1) :
    proofRewriteAtZero.eval (Nat.pair 1 (Encodable.encode φ)) = Encodable.encode φ.free := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_proofRewriteAtZero]
  simp only [arithmeticPair_nat, evalArithmetic_nat]
  rw [proofRewriteCode_encode, proofRewNatFormula_free]

theorem proofRewriteAtZero_subst_encode (k : ℕ) (φ : Semiproposition ℒₛₑₜ 1) :
    proofRewriteAtZero.eval (Nat.pair (k + 2) (Encodable.encode φ)) = Encodable.encode (φ/[&k] : SetTheoryProposition) := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_proofRewriteAtZero]
  simp only [arithmeticPair_nat, evalArithmetic_nat]
  rw [proofRewriteCode_encode, proofRewNatFormula_subst]

theorem proofRewriteSequent_shift_encode (Γ : Sequent ℒₛₑₜ) :
    proofRewriteSequent.eval (Nat.pair 0 (Encodable.encode Γ)) = Encodable.encode (Γ.map Semiformula.shift) :=
  listMap_encode proofRewriteAtZero Semiformula.shift 0 proofRewriteAtZero_shift_encode Γ

end PrimitiveProgram
end ZFVP
