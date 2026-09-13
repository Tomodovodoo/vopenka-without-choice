import ZFVP.ModelTheory.InternalPeano
import ZFVP.SetTheory.StandardNaturals
import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Data.Nat.Pairing

/-! Mathlib's natural-number pairing extends to every element of internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

def naturalSquarePairFormula : SetTheorySemisentence 3 :=
  f“z x y. (x ∈ y ∧ z = !ordinalAddFormula (!naturalMulFormula y y) x) ∨
    (x ∉ y ∧ z = !ordinalAddFormula (!ordinalAddFormula (!naturalMulFormula x x) x) y)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalSquarePair (x y : V) : V := by
  classical
  exact if x ∈ y then ordinalAdd (naturalMul y y) x else ordinalAdd (ordinalAdd (naturalMul x x) x) y

instance naturalSquarePair_defined : ℒₛₑₜ-function₂[V] naturalSquarePair via naturalSquarePairFormula :=
  ⟨fun v ↦ by
    by_cases h : v 1 ∈ v 2 <;> simp [naturalSquarePairFormula, naturalSquarePair, h]⟩

instance naturalSquarePair_definable : ℒₛₑₜ-function₂[V] naturalSquarePair :=
  naturalSquarePair_defined.to_definable

theorem naturalSquarePair_natural {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    naturalSquarePair x y ∈ (ω : V) := by
  unfold naturalSquarePair
  split
  · exact ordinalAdd_natural (naturalMul_natural hy hy) hx
  · exact ordinalAdd_natural (ordinalAdd_natural (naturalMul_natural hx hx) hx) hy

instance internalArithmetic_models_IOpen : (InternalArithmetic V)↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := by
  let : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗣𝗔 := Entailment.WeakerThan.ofSubset
    (Set.union_subset_union_right _ (InductionScheme_subset (fun _ ↦ trivial)))
  exact ModelsTheory.of_provably_subtheory (InternalArithmetic V) 𝗜𝗢𝗽𝗲𝗻 𝗣𝗔 inferInstance

theorem internalArithmetic_le (x y : InternalArithmetic V) :
    x ≤ y ↔ internalArithmeticVal x ⊆ internalArithmeticVal y := by
  let := IsOrdinal.of_mem (internalArithmeticVal_mem x)
  let := IsOrdinal.of_mem (internalArithmeticVal_mem y)
  rw [le_iff_lt_or_eq, internalArithmetic_lt, internalArithmetic_eq, IsOrdinal.subset_iff]
  exact or_comm

theorem internalArithmeticVal_pair (x y : InternalArithmetic V) :
    internalArithmeticVal (Arithmetic.pair x y) = naturalSquarePair (internalArithmeticVal x) (internalArithmeticVal y) := by
  by_cases h : x < y
  · have hv := (internalArithmetic_lt x y).mp h
    simp [Arithmetic.pair, naturalSquarePair, h, hv]
  · have hv : internalArithmeticVal x ∉ internalArithmeticVal y :=
      fun hm ↦ h ((internalArithmetic_lt x y).mpr hm)
    simp [Arithmetic.pair, naturalSquarePair, h, hv]

theorem naturalSquarePair_injective {a b c d : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hd : d ∈ (ω : V))
    (he : naturalSquarePair a b = naturalSquarePair c d) : a = c ∧ b = d := by
  obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨y, rfl⟩ := internalArithmeticVal_surjective hb
  obtain ⟨z, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hd
  have hp : Arithmetic.pair x y = Arithmetic.pair z w :=
    internalArithmeticVal_injective (by simpa only [internalArithmeticVal_pair] using he)
  have hu := congrArg Arithmetic.unpair hp
  simp only [Arithmetic.unpair_pair, Prod.mk.injEq] at hu
  exact ⟨congrArg internalArithmeticVal hu.1, congrArg internalArithmeticVal hu.2⟩

theorem naturalSquarePair_surjective {n : V} (hn : n ∈ (ω : V)) :
    ∃ a ∈ (ω : V), ∃ b ∈ (ω : V), naturalSquarePair a b = n := by
  obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective hn
  refine ⟨internalArithmeticVal (Arithmetic.pi₁ x), internalArithmeticVal_mem _,
    internalArithmeticVal (Arithmetic.pi₂ x), internalArithmeticVal_mem _, ?_⟩
  rw [← internalArithmeticVal_pair, Arithmetic.pair_unpair]

theorem naturalSquarePair_natCast (m n : ℕ) :
    naturalSquarePair (m : V) (n : V) = ((Nat.pair m n : ℕ) : V) := by
  simp only [naturalSquarePair, natCast_mem_iff, Nat.pair]
  split <;> simp only [naturalMul_natCast, ordinalAdd_natCast]

end ZFVP
