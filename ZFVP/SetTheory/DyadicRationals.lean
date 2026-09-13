import ZFVP.SetTheory.NaturalPower
import ZFVP.SetTheory.InternalRationalBounds

/-! Dyadic units indexed by every natural number of the model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def dyadicUnitFormula : SetTheorySemisentence 2 :=
  f“q n. q = !rationalInvFormula (!rationalNaturalFormula
    (!naturalPowFormula (!succ.dfn (!succ.dfn (!isEmpty))) n))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def dyadicUnit (n : V) : V := rationalInv (rationalNatural (naturalPow (2 : V) n))

instance dyadicUnitFormula_defined : ℒₛₑₜ-function₁[V] dyadicUnit via dyadicUnitFormula :=
  ⟨fun v ↦ by simp [dyadicUnitFormula, dyadicUnit]; rfl⟩

instance dyadicUnit_definable : ℒₛₑₜ-function₁[V] dyadicUnit := dyadicUnitFormula_defined.to_definable

theorem dyadicUnit_mem {n : V} (hn : n ∈ (ω : V)) : dyadicUnit n ∈ internalRationals V :=
  rationalInv_mem (rationalNatural_mem (naturalPow_natural (by simp) hn))

namespace InternalNatural

noncomputable def powerTwo (n : InternalNatural V) : InternalNatural V :=
  ⟨naturalPow (2 : V) n.val, naturalPow_natural (by simp) n.property⟩

@[simp] theorem powerTwo_zero : powerTwo (0 : InternalNatural V) = 1 :=
  Subtype.ext (naturalPow_zero _)

theorem powerTwo_succ (n : InternalNatural V) : powerTwo (n + 1) = powerTwo n * 2 := by
  apply Subtype.ext
  change naturalPow (2 : V) (ordinalAdd n.val 1) = naturalMul (naturalPow (2 : V) n.val) 2
  rw [ordinalAdd_one_natural n.property, naturalPow_succ _ n.property]

theorem powerTwo_add (n m : InternalNatural V) : powerTwo (n + m) = powerTwo n * powerTwo m :=
  Subtype.ext (naturalPow_add (by simp) n.property m.property)

theorem powerTwo_pos (n : InternalNatural V) : 0 < powerTwo n :=
  naturalPow_positive (by simp) (by simp) n.property

theorem succ_le_powerTwo (n : InternalNatural V) : n + 1 ≤ powerTwo n := by
  change ordinalAdd n.val 1 ⊆ naturalPow (2 : V) n.val
  rw [ordinalAdd_one_natural n.property]
  exact naturalPow_two_growth n.property

end InternalNatural

namespace InternalRational

@[simp] theorem ofNatural_natCast (n : ℕ) : ofNatural (n : InternalNatural V) = (n : InternalRational V) :=
  rfl

noncomputable def dyadic (n : InternalNatural V) : InternalRational V :=
  (ofNatural n.powerTwo)⁻¹

@[simp] theorem val_dyadic (n : InternalNatural V) : (dyadic n).val = dyadicUnit n.val := rfl

@[simp] theorem dyadic_zero : dyadic (0 : InternalNatural V) = 1 := by
  simp [dyadic]

theorem dyadic_pos (n : InternalNatural V) : 0 < dyadic n :=
  inv_pos.mpr ((ofNatural_pos_iff _).mpr (InternalNatural.powerTwo_pos n))

theorem dyadic_le_one (n : InternalNatural V) : dyadic n ≤ 1 := by
  have hp := (ofNatural_pos_iff _).mpr (InternalNatural.powerTwo_pos n)
  have h1 : (1 : InternalRational V) ≤ ofNatural n.powerTwo := by
    simpa only [ofNatural_one] using (ofNatural_le_iff 1 n.powerTwo).mpr
      (InternalNatural.one_le_of_pos (InternalNatural.powerTwo_pos n))
  simpa only [dyadic, inv_one] using (inv_le_inv₀ hp zero_lt_one).mpr h1

theorem dyadic_succ (n : InternalNatural V) : dyadic (n + 1) = dyadic n / 2 := by
  simp only [dyadic, InternalNatural.powerTwo_succ, ofNatural_mul,
    mul_inv_rev, div_eq_mul_inv]
  exact mul_comm _ _

theorem dyadic_add (n m : InternalNatural V) : dyadic (n + m) = dyadic n * dyadic m := by
  simp only [dyadic, InternalNatural.powerTwo_add, ofNatural_mul, mul_inv_rev]
  exact mul_comm _ _

theorem dyadic_halves (n : InternalNatural V) : dyadic (n + 1) + dyadic (n + 1) = dyadic n := by
  rw [dyadic_succ]
  exact add_halves _

theorem dyadic_succ_lt (n : InternalNatural V) : dyadic (n + 1) < dyadic n := by
  rw [dyadic_succ]
  exact div_lt_self (dyadic_pos n) one_lt_two

theorem dyadic_antitone {n m : InternalNatural V} (hnm : n ≤ m) : dyadic m ≤ dyadic n := by
  obtain ⟨d, hd, he⟩ := ordinalAdd_difference_natural n.property m.property hnm
  have he' : n + (⟨d, hd⟩ : InternalNatural V) = m := Subtype.ext he
  rw [← he', dyadic_add]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (dyadic_le_one (⟨d, hd⟩ : InternalNatural V)) (le_of_lt (dyadic_pos n))

theorem exists_dyadic_lt {q : InternalRational V} (hq : 0 < q) :
    ∃ n : InternalNatural V, dyadic n < q := by
  obtain ⟨n, hn, hnq⟩ := exists_small_natural_inverse hq
  have hnp : n < n.powerTwo := lt_of_lt_of_le (lt_add_one n) (InternalNatural.succ_le_powerTwo n)
  have hi : dyadic n < (ofNatural n)⁻¹ :=
    (inv_lt_inv₀ ((ofNatural_pos_iff _).mpr (InternalNatural.powerTwo_pos n))
      ((ofNatural_pos_iff _).mpr hn)).mpr ((ofNatural_lt_iff _ _).mpr hnp)
  exact ⟨n, lt_trans hi hnq⟩

end InternalRational

theorem dyadicUnit_positive {n : V} (hn : n ∈ (ω : V)) :
    InternalRationalLT (rationalZero V) (dyadicUnit n) :=
  InternalRational.dyadic_pos (⟨n, hn⟩ : InternalNatural V)

theorem dyadicUnit_small {q : V} (hq : q ∈ internalRationals V)
    (hqp : InternalRationalLT (rationalZero V) q) :
    ∃ n ∈ (ω : V), InternalRationalLT (dyadicUnit n) q := by
  obtain ⟨n, hn⟩ := InternalRational.exists_dyadic_lt (q := (⟨q, hq⟩ : InternalRational V)) hqp
  exact ⟨n.val, n.property, hn⟩

end ZFVP
