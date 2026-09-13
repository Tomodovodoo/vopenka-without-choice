import ZFVP.ModelTheory.InternalArithmeticModel
import ZFVP.SetTheory.NaturalArithmeticOrder
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-! ZF's internal omega satisfies all axioms of arithmetic without induction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalArithmetic_zero_le (x : InternalArithmetic V) : 0 = x ∨ 0 < x := by
  let := IsOrdinal.of_mem (internalArithmeticVal_mem x)
  have h := IsOrdinal.subset_iff.mp (empty_subset (internalArithmeticVal x))
  simpa only [internalArithmetic_eq, internalArithmetic_lt, internalArithmeticVal_zero, zero_def] using h

theorem internalArithmetic_one_le {x : InternalArithmetic V} (hx : 0 < x) : 1 = x ∨ 1 < x := by
  let := IsOrdinal.of_mem (internalArithmeticVal_mem x)
  have hsub : (1 : V) ⊆ internalArithmeticVal x := by
    intro z hz
    have hz0 : z = 0 := by
      change z ∈ succ (0 : V) at hz
      simpa only [mem_succ_iff, zero_def, not_mem_empty, or_false] using hz
    rw [hz0]
    simpa using (internalArithmetic_lt _ _).mp hx
  let := IsOrdinal.of_mem (by simp : (1 : V) ∈ ω)
  have h := IsOrdinal.subset_iff.mp hsub
  simpa only [internalArithmetic_eq, internalArithmetic_lt, internalArithmeticVal_one] using h

theorem internalArithmetic_add_difference {x y : InternalArithmetic V} (hxy : x < y) :
    ∃ z : InternalArithmetic V, x + z = y := by
  let := IsOrdinal.of_mem (internalArithmeticVal_mem y)
  have hsub := IsOrdinal.toIsTransitive.transitive _ ((internalArithmetic_lt _ _).mp hxy)
  obtain ⟨c, hc, he⟩ := ordinalAdd_difference_natural (internalArithmeticVal_mem x) (internalArithmeticVal_mem y) hsub
  obtain ⟨z, hz⟩ := internalArithmeticVal_surjective hc
  refine ⟨z, internalArithmeticVal_injective ?_⟩
  rw [internalArithmeticVal_add, hz]
  exact he

instance internalArithmetic_models_PeanoMinus : (InternalArithmetic V)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  apply models_theory_iff.mpr
  intro φ hφ
  cases hφ with
  | equal ψ hψ => exact Theory.models (InternalArithmetic V) (𝗘𝗤 ℒₒᵣ) hψ
  | addZero =>
    suffices ∀ a : InternalArithmetic V, a + 0 = a by simpa [models_iff]
    intro a
    apply internalArithmeticVal_injective
    simp [zero_def, ordinalAdd_zero]
  | addAssoc =>
    suffices ∀ a b c : InternalArithmetic V, (a + b) + c = a + (b + c) by simpa [models_iff]
    intro a b c
    apply internalArithmeticVal_injective
    simp only [internalArithmeticVal_add]
    exact ordinalAdd_assoc_natural (internalArithmeticVal_mem a) (internalArithmeticVal_mem b) (internalArithmeticVal_mem c)
  | addComm =>
    suffices ∀ a b : InternalArithmetic V, a + b = b + a by simpa [models_iff]
    intro a b
    apply internalArithmeticVal_injective
    simp only [internalArithmeticVal_add]
    exact ordinalAdd_comm_natural (internalArithmeticVal_mem a) (internalArithmeticVal_mem b)
  | addEqOfLt =>
    suffices ∀ a b : InternalArithmetic V, a < b → ∃ c, a + c = b by simpa [models_iff]
    intro a b h; exact internalArithmetic_add_difference h
  | zeroLe => simpa [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT] using internalArithmetic_zero_le (V := V)
  | zeroLtOne => simp [models_iff]
  | oneLeOfZeroLt =>
    suffices ∀ a : InternalArithmetic V, 0 < a → 1 = a ∨ 1 < a by
      simpa [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT]
    intro a h; exact internalArithmetic_one_le h
  | addLtAdd =>
    suffices ∀ a b c : InternalArithmetic V, a < b → a + c < b + c by simpa [models_iff]
    intro a b c h
    rw [internalArithmetic_lt, internalArithmeticVal_add, internalArithmeticVal_add]
    exact ordinalAdd_lt_first_natural (internalArithmeticVal_mem a) (internalArithmeticVal_mem b)
      (internalArithmeticVal_mem c) ((internalArithmetic_lt _ _).mp h)
  | mulZero =>
    suffices ∀ a : InternalArithmetic V, a * 0 = 0 by simpa [models_iff]
    intro a
    apply internalArithmeticVal_injective
    simp
  | mulOne =>
    suffices ∀ a : InternalArithmetic V, a * 1 = a by simpa [models_iff]
    intro a
    apply internalArithmeticVal_injective
    simpa using naturalMul_one (internalArithmeticVal_mem a)
  | mulAssoc =>
    suffices ∀ a b c : InternalArithmetic V, (a * b) * c = a * (b * c) by simpa [models_iff]
    intro a b c
    apply internalArithmeticVal_injective
    simp only [internalArithmeticVal_mul]
    exact naturalMul_assoc (internalArithmeticVal_mem a) (internalArithmeticVal_mem b) (internalArithmeticVal_mem c)
  | mulComm =>
    suffices ∀ a b : InternalArithmetic V, a * b = b * a by simpa [models_iff]
    intro a b
    apply internalArithmeticVal_injective
    simp only [internalArithmeticVal_mul]
    exact naturalMul_comm (internalArithmeticVal_mem a) (internalArithmeticVal_mem b)
  | mulLtMul =>
    suffices ∀ a b c : InternalArithmetic V, a < b ∧ 0 < c → a * c < b * c by simpa [models_iff]
    rintro a b c ⟨hab, hc⟩
    rw [internalArithmetic_lt, internalArithmeticVal_mul, internalArithmeticVal_mul]
    exact naturalMul_lt_first (internalArithmeticVal_mem a) (internalArithmeticVal_mem b)
      (internalArithmeticVal_mem c) ((internalArithmetic_lt _ _).mp hab) (by simpa using (internalArithmetic_lt _ _).mp hc)
  | distr =>
    suffices ∀ a b c : InternalArithmetic V, a * (b + c) = a * b + a * c by simpa [models_iff]
    intro a b c
    apply internalArithmeticVal_injective
    simp only [internalArithmeticVal_add, internalArithmeticVal_mul]
    exact naturalMul_add_right (internalArithmeticVal_mem a) (internalArithmeticVal_mem b) (internalArithmeticVal_mem c)
  | ltIrrefl => simp [models_iff]
  | ltTrans =>
    suffices ∀ a b c : InternalArithmetic V, a < b ∧ b < c → a < c by simpa [models_iff]
    rintro a b c ⟨hab, hbc⟩
    let := IsOrdinal.of_mem (internalArithmeticVal_mem c)
    exact (internalArithmetic_lt _ _).mpr
      (IsOrdinal.toIsTransitive.mem_trans ((internalArithmetic_lt _ _).mp hab) ((internalArithmetic_lt _ _).mp hbc))
  | ltTri =>
    suffices ∀ a b : InternalArithmetic V, a < b ∨ a = b ∨ b < a by simpa [models_iff]
    intro a b
    let := IsOrdinal.of_mem (internalArithmeticVal_mem a)
    let := IsOrdinal.of_mem (internalArithmeticVal_mem b)
    simpa only [internalArithmetic_lt, internalArithmetic_eq] using
      IsOrdinal.mem_trichotomy (internalArithmeticVal a) (internalArithmeticVal b)

end ZFVP
