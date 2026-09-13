import ZFVP.Syntax.PrimitiveProgramLKComposition
import ZFVP.Syntax.PrimitiveProgramLKStandardCertificate
import ZFVP.Syntax.ArithmeticPrimitiveProgramNumerals

/-! Standard syntax checks and logical certificates hold in every internal arithmetic model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCheck_encode_natCast {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hfree : ∀ _ : ξ, allowFree = true) {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    (formulaCheck allowFree).evalArithmetic (Arithmetic.pair (n : M) (Encodable.encode φ : M)) = 1 := by
  rw [arithmeticPair_natCast, evalArithmetic_natCast, formulaCheck_encode allowFree hfree φ]
  simp

theorem sequentCheck_encode_natCast {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hfree : ∀ _ : ξ, allowFree = true) {n : ℕ} (Γ : List (Semiformula ℒₛₑₜ ξ n)) :
    (sequentCheck allowFree).evalArithmetic (Arithmetic.pair (n : M) (Encodable.encode Γ : M)) = 1 := by
  rw [arithmeticPair_natCast, evalArithmetic_natCast, sequentCheck_encode allowFree hfree Γ]
  simp

theorem negateCode_encode_natCast {ξ : Type*} [Encodable ξ] {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    negateCode.evalArithmetic (Encodable.encode φ : M) = (Encodable.encode (∼φ) : M) := by
  rw [evalArithmetic_natCast, negateCode_encode]

theorem encodeList_cons_natCast {α : Type*} [Encodable α] (a : α) (as : List α) :
    (Encodable.encode (a :: as) : M) = Arithmetic.pair (Encodable.encode a : M) (Encodable.encode as : M) + 1 := by
  rw [Encodable.encode_list_cons]
  simp [← arithmeticPair_natCast]

theorem programLKProvable_of_derivation (C : Sequent ℒₛₑₜ) (h : Nonempty (Derivation C)) :
    ProgramLKProvable (Encodable.encode C : M) := by
  obtain ⟨p, hp⟩ := (exists_lkProofCheck_encode_iff C).mpr h
  refine ⟨(Encodable.encode p : M), ?_⟩
  rw [arithmeticPair_natCast, evalArithmetic_natCast, hp]
  simp

end PrimitiveProgram
end ZFVP
