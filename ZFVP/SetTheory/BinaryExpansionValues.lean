import ZFVP.SetTheory.BinaryExpansionNumerator

/-! Rational endpoints of the closed intervals specified by binary prefixes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryValueFormula : SetTheorySemisentence 3 :=
  f“q c n. q = !rationalMulFormula (!rationalNaturalFormula (!binaryNumeratorFormula c n))
    (!dyadicUnitFormula n)”

def binaryUpperFormula : SetTheorySemisentence 3 :=
  f“q c n. q = !rationalAddFormula (!binaryValueFormula c n) (!dyadicUnitFormula n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryValue (c n : V) : V :=
  rationalMul (rationalNatural (binaryNumerator c n)) (dyadicUnit n)

noncomputable def binaryUpper (c n : V) : V := rationalAdd (binaryValue c n) (dyadicUnit n)

instance binaryValueFormula_defined : ℒₛₑₜ-function₂[V] binaryValue via binaryValueFormula :=
  ⟨fun v ↦ by simp [binaryValueFormula, binaryValue]⟩

instance binaryValue_definable : ℒₛₑₜ-function₂[V] binaryValue := binaryValueFormula_defined.to_definable

instance binaryUpperFormula_defined : ℒₛₑₜ-function₂[V] binaryUpper via binaryUpperFormula :=
  ⟨fun v ↦ by simp [binaryUpperFormula, binaryUpper]⟩

instance binaryUpper_definable : ℒₛₑₜ-function₂[V] binaryUpper := binaryUpperFormula_defined.to_definable

theorem binaryValue_mem {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryValue c n ∈ internalRationals V :=
  rationalMul_mem (rationalNatural_mem (binaryNumerator_bound_of_cantor hc hn).1) (dyadicUnit_mem hn)

theorem binaryUpper_mem {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryUpper c n ∈ internalRationals V := rationalAdd_mem (binaryValue_mem hc hn) (dyadicUnit_mem hn)

namespace InternalNatural

noncomputable def binaryNumeratorOf (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    InternalNatural V := ⟨binaryNumerator c n.val, (binaryNumerator_bound_of_cantor hc n.property).1⟩

noncomputable def binaryDigitOf (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    InternalNatural V :=
  ⟨c ‘ n.val, IsTransitive.ω.transitive _ (by simp) _ (function_value_mem hc n.property)⟩

theorem binaryDigitOf_lt_two (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryDigitOf c hc n < 2 := function_value_mem hc n.property

theorem binaryDigitOf_le_one (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryDigitOf c hc n ≤ 1 := by
  have h := add_one_le_of_lt (binaryDigitOf_lt_two c hc n)
  have h' : binaryDigitOf c hc n + 1 ≤ (1 : InternalNatural V) + 1 := by
    simpa only [one_add_one_eq_two] using h
  exact le_of_add_le_add_right h'

@[simp] theorem binaryNumeratorOf_zero (c : V) (hc : c ∈ cantorSpace V) :
    binaryNumeratorOf c hc 0 = 0 := Subtype.ext (binaryNumerator_zero c)

theorem binaryNumeratorOf_succ (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryNumeratorOf c hc (n + 1) = binaryNumeratorOf c hc n + binaryNumeratorOf c hc n +
      binaryDigitOf c hc n := by
  apply Subtype.ext
  change binaryNumerator c (ordinalAdd n.val 1) =
    ordinalAdd (ordinalAdd (binaryNumerator c n.val) (binaryNumerator c n.val)) (c ‘ n.val)
  rw [ordinalAdd_one_natural n.property, binaryNumerator_succ _ n.property]

theorem binaryNumeratorOf_lt_powerTwo (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryNumeratorOf c hc n < n.powerTwo := (binaryNumerator_bound_of_cantor hc n.property).2

end InternalNatural

namespace InternalRational

noncomputable def binaryApprox (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    InternalRational V := ofNatural (InternalNatural.binaryNumeratorOf c hc n) * dyadic n

@[simp] theorem val_binaryApprox (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    (binaryApprox c hc n).val = binaryValue c n.val := rfl

@[simp] theorem binaryApprox_zero (c : V) (hc : c ∈ cantorSpace V) : binaryApprox c hc 0 = 0 := by
  simp [binaryApprox]

theorem binaryApprox_nonneg (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    0 ≤ binaryApprox c hc n := mul_nonneg (ofNatural_nonneg _) (le_of_lt (dyadic_pos n))

theorem binaryApprox_lt_one (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryApprox c hc n < 1 := by
  have hnum := (ofNatural_lt_iff _ _).mpr (InternalNatural.binaryNumeratorOf_lt_powerTwo c hc n)
  have h := mul_lt_mul_of_pos_right hnum (dyadic_pos n)
  have hp := (ofNatural_pos_iff _).mpr (InternalNatural.powerTwo_pos n)
  simpa only [binaryApprox, dyadic, mul_inv_cancel₀ (ne_of_gt hp)] using h

theorem binaryApprox_upper_le_one (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryApprox c hc n + dyadic n ≤ 1 := by
  have hnum := (ofNatural_le_iff _ _).mpr
    (InternalNatural.add_one_le_of_lt (InternalNatural.binaryNumeratorOf_lt_powerTwo c hc n))
  rw [ofNatural_add, ofNatural_one] at hnum
  have h := mul_le_mul_of_nonneg_right hnum (le_of_lt (dyadic_pos n))
  have hp := (ofNatural_pos_iff _).mpr (InternalNatural.powerTwo_pos n)
  simpa only [add_mul, one_mul, binaryApprox, dyadic, mul_inv_cancel₀ (ne_of_gt hp)] using h

theorem binaryApprox_succ (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryApprox c hc (n + 1) = binaryApprox c hc n +
      ofNatural (InternalNatural.binaryDigitOf c hc n) * dyadic (n + 1) := by
  simp only [binaryApprox, InternalNatural.binaryNumeratorOf_succ, ofNatural_add]
  rw [← dyadic_halves n]
  ring

theorem binaryApprox_step (c : V) (hc : c ∈ cantorSpace V) (n : InternalNatural V) :
    binaryApprox c hc n ≤ binaryApprox c hc (n + 1) ∧
      binaryApprox c hc (n + 1) + dyadic (n + 1) ≤ binaryApprox c hc n + dyadic n := by
  have hbit0 := ofNatural_nonneg (InternalNatural.binaryDigitOf c hc n)
  have hbit1 : ofNatural (InternalNatural.binaryDigitOf c hc n) ≤ (1 : InternalRational V) := by
    simpa only [ofNatural_one] using
      (ofNatural_le_iff _ _).mpr (InternalNatural.binaryDigitOf_le_one c hc n)
  constructor
  · rw [binaryApprox_succ]
    exact le_add_of_nonneg_right (mul_nonneg hbit0 (le_of_lt (dyadic_pos _)))
  · rw [binaryApprox_succ]
    calc
      binaryApprox c hc n + ofNatural (InternalNatural.binaryDigitOf c hc n) * dyadic (n + 1) +
          dyadic (n + 1) ≤ binaryApprox c hc n + 1 * dyadic (n + 1) + dyadic (n + 1) :=
        add_le_add_left (add_le_add_right
          (mul_le_mul_of_nonneg_right hbit1 (le_of_lt (dyadic_pos _))) _) _
      _ = binaryApprox c hc n + dyadic n := by rw [one_mul, add_assoc, dyadic_halves]

end InternalRational

theorem binaryValue_zero (c : V) : binaryValue c 0 = rationalZero V := by
  rw [binaryValue, binaryNumerator_zero, rationalNatural_zero]
  rw [rationalMul_comm rationalZero_mem (dyadicUnit_mem (by simp)),
    rationalMul_zero (dyadicUnit_mem (by simp))]

theorem binaryValues_step {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    ¬ InternalRationalLT (binaryValue c (succ n)) (binaryValue c n) ∧
      ¬ InternalRationalLT (binaryUpper c n) (binaryUpper c (succ n)) := by
  have h := InternalRational.binaryApprox_step c hc (⟨n, hn⟩ : InternalNatural V)
  change ¬ InternalRationalLT (binaryValue c (ordinalAdd n 1)) (binaryValue c n) ∧
    ¬ InternalRationalLT (binaryUpper c n) (binaryUpper c (ordinalAdd n 1)) at h
  rwa [ordinalAdd_one_natural hn] at h

end ZFVP
