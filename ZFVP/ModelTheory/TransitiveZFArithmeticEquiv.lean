import ZFVP.ModelTheory.TransitiveZFArithmetic

/-! The entire interpreted arithmetic is invariant under passage to a transitive ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def arithmeticMap (x : InternalArithmetic (SetDomain U)) : InternalArithmetic V :=
  ⟨⟨(internalArithmeticVal x).val,
    (arithmeticInZF_domain _).mpr ((natural_iff U _).mp (internalArithmeticVal_mem x))⟩⟩

@[simp] theorem arithmeticMap_val (x : InternalArithmetic (SetDomain U)) :
    internalArithmeticVal (arithmeticMap U x) = (internalArithmeticVal x).val := rfl

theorem arithmeticMap_injective : Function.Injective (arithmeticMap U) := by
  intro x y h
  apply internalArithmeticVal_injective
  apply Subtype.val_injective
  exact congrArg internalArithmeticVal h

theorem arithmeticMap_surjective : Function.Surjective (arithmeticMap U) := by
  intro y
  let n : SetDomain U := ⟨internalArithmeticVal y, natural_mem U (internalArithmeticVal_mem y)⟩
  have hn : n ∈ (ω : SetDomain U) := (natural_iff U n).mpr (internalArithmeticVal_mem y)
  obtain ⟨x, hx⟩ := internalArithmeticVal_surjective hn
  refine ⟨x, internalArithmeticVal_injective ?_⟩
  rw [arithmeticMap_val, hx]

@[simp] theorem arithmeticMap_zero : arithmeticMap U 0 = 0 := by
  apply internalArithmeticVal_injective
  simp only [arithmeticMap_val, internalArithmeticVal_zero, zero_def, empty_val]

@[simp] theorem arithmeticMap_one : arithmeticMap U 1 = 1 := by
  apply internalArithmeticVal_injective
  simp only [arithmeticMap_val, internalArithmeticVal_one]
  exact numeral_val U 1

@[simp] theorem arithmeticMap_add (x y : InternalArithmetic (SetDomain U)) :
    arithmeticMap U (x + y) = arithmeticMap U x + arithmeticMap U y := by
  apply internalArithmeticVal_injective
  simp only [arithmeticMap_val, internalArithmeticVal_add]
  exact ordinalAdd_val U _ _ (internalArithmeticVal_mem x) (internalArithmeticVal_mem y)

@[simp] theorem arithmeticMap_mul (x y : InternalArithmetic (SetDomain U)) :
    arithmeticMap U (x * y) = arithmeticMap U x * arithmeticMap U y := by
  apply internalArithmeticVal_injective
  simp only [arithmeticMap_val, internalArithmeticVal_mul]
  exact naturalMul_val U _ _ (internalArithmeticVal_mem x) (internalArithmeticVal_mem y)

theorem arithmeticMap_lt_iff (x y : InternalArithmetic (SetDomain U)) :
    x < y ↔ arithmeticMap U x < arithmeticMap U y := by
  simp only [internalArithmetic_lt, arithmeticMap_val]
  rfl

noncomputable def arithmeticEquiv : InternalArithmetic (SetDomain U) ≃ InternalArithmetic V :=
  Equiv.ofBijective (arithmeticMap U) ⟨arithmeticMap_injective U, arithmeticMap_surjective U⟩

theorem arithmetic_elementaryEquiv : InternalArithmetic (SetDomain U) ≡ₑ[ℒₒᵣ] InternalArithmetic V := by
  apply Structure.ElementaryEquiv.of_equiv (arithmeticEquiv U)
  · intro k r v₁ v₂ hv
    change ∀ i, arithmeticMap U (v₁ i) = v₂ i at hv
    cases r with
    | eq =>
      change v₁ 0 = v₁ 1 ↔ v₂ 0 = v₂ 1
      rw [← hv 0, ← hv 1]
      exact (arithmeticMap_injective U).eq_iff.symm
    | lt =>
      change v₁ 0 < v₁ 1 ↔ v₂ 0 < v₂ 1
      rw [← hv 0, ← hv 1]
      exact arithmeticMap_lt_iff U _ _
  · intro k f v₁ v₂ hv
    change ∀ i, arithmeticMap U (v₁ i) = v₂ i at hv
    cases f with
    | zero => exact arithmeticMap_zero U
    | one => exact arithmeticMap_one U
    | add =>
      change arithmeticMap U (v₁ 0 + v₁ 1) = v₂ 0 + v₂ 1
      rw [arithmeticMap_add, hv 0, hv 1]
    | mul =>
      change arithmeticMap U (v₁ 0 * v₁ 1) = v₂ 0 * v₂ 1
      rw [arithmeticMap_mul, hv 0, hv 1]

theorem arithmetic_translation_absolute (φ : ArithmeticSentence) :
    (SetDomain U)↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate φ ↔ V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate φ := by
  rw [internalArithmetic_translation, internalArithmetic_translation]
  exact (arithmetic_elementaryEquiv U).models

end TransitiveZF
end ZFVP
