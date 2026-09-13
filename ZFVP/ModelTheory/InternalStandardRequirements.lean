import ZFVP.ModelTheory.InternalSyntaxChecks
import ZFVP.ModelTheory.InternalProgramForwardTabulate
import ZFVP.Syntax.PrimitiveProgramRequirementsStandard

/-! Standard formula codes satisfy the internal checks in every larger natural context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem requirementFits_mono {r n m : V} (hr : r ∈ (ω : V))
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) (hv : requirementFits r n) :
    requirementFits r m := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨n₀, rfl⟩ := internalArithmeticVal_surjective hn
  obtain ⟨m₀, rfl⟩ := internalArithmeticVal_surjective hm
  rw [requirementFits_val] at hv ⊢
  have hnm' := (internalArithmetic_le n₀ m₀).mpr hnm
  exact ⟨hv.1, le_trans hv.2 (by simpa only [add_comm] using add_le_add_right hnm' 1)⟩

theorem requirementFits_encode {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hfree : ∀ _ : ξ, allowFree = true) {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    requirementFits ((formulaRequirement allowFree).evalSet (Encodable.encode φ : V)) (n : V) := by
  have hnat : (formulaCheck allowFree).eval (Nat.pair n (Encodable.encode φ)) = 1 := by
    rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_formulaCheck_eq_one, arithmeticLE_nat]
    exact formulaRequirement_encode_valid allowFree hfree φ
  apply (evalSet_formulaCheck_eq_one allowFree (by simp) (by simp)).mp
  rw [naturalSquarePair_natCast, evalSet_natCast, hnat]
  rfl

theorem requirementFits_encode_prefix {m : ℕ} (φ : SetTheorySemisentence m) {n : V} (hn : n ∈ (ω : V)) :
    requirementFits ((formulaRequirement false).evalSet (Encodable.encode φ : V)) (prefixSize m n) := by
  apply requirementFits_mono (evalSet_natural _ (by simp)) (by simp) (prefixSize_natural m hn) ?_
    (requirementFits_encode false Empty.elim φ)
  intro i hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff i m).mp hi
  exact natCast_mem_prefixSize hn j

end ZFVP
