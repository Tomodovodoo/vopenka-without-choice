import ZFVP.SetTheory.NaturalArithmeticOrder
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Defs

/-! Algebraic operations on the whole internal omega. The semiring laws come
from the definable internal inductions in NaturalArithmeticLaws. This interface
allows algebraic proofs about rational codes without restricting their entries
to standard numerals. It does not identify the model's omega with Lean's Nat. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev InternalNatural (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] := {n : V // n ∈ (ω : V)}

namespace InternalNatural

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable instance : Zero (InternalNatural V) := ⟨⟨0, by simp⟩⟩
noncomputable instance : One (InternalNatural V) := ⟨⟨1, by simp⟩⟩

noncomputable instance : Add (InternalNatural V) :=
  ⟨fun a b ↦ ⟨ordinalAdd a.val b.val, ordinalAdd_natural a.property b.property⟩⟩

noncomputable instance : Mul (InternalNatural V) :=
  ⟨fun a b ↦ ⟨naturalMul a.val b.val, naturalMul_natural a.property b.property⟩⟩

noncomputable instance : CommSemiring (InternalNatural V) where
  add_assoc a b c := Subtype.ext (ordinalAdd_assoc_natural a.property b.property c.property)
  zero_add a := Subtype.ext (ordinalAdd_zero_left_natural a.property)
  add_zero a := Subtype.ext (ordinalAdd_zero a.val)
  add_comm a b := Subtype.ext (ordinalAdd_comm_natural a.property b.property)
  mul_assoc a b c := Subtype.ext (naturalMul_assoc a.property b.property c.property)
  one_mul a := Subtype.ext (naturalMul_one_left a.property)
  mul_one a := Subtype.ext (naturalMul_one a.property)
  mul_comm a b := Subtype.ext (naturalMul_comm a.property b.property)
  zero_mul a := Subtype.ext (naturalMul_zero_left a.property)
  mul_zero a := Subtype.ext (naturalMul_zero a.val)
  left_distrib a b c := Subtype.ext (naturalMul_add_right a.property b.property c.property)
  right_distrib a b c := by
    apply Subtype.ext
    change naturalMul (ordinalAdd a.val b.val) c.val =
      ordinalAdd (naturalMul a.val c.val) (naturalMul b.val c.val)
    rw [naturalMul_comm (ordinalAdd_natural a.property b.property) c.property,
      naturalMul_add_right c.property a.property b.property,
      naturalMul_comm c.property a.property, naturalMul_comm c.property b.property]
  nsmul := nsmulRec
  npow := npowRec
  natCast n := ⟨(n : V), by simp⟩
  natCast_zero := rfl
  natCast_succ n := by
    apply Subtype.ext
    change ((n + 1 : ℕ) : V) = ordinalAdd (n : V) 1
    rw [num_succ_def, ordinalAdd_one_natural (by simp)]

@[simp] theorem val_zero : (0 : InternalNatural V).val = (0 : V) := rfl
@[simp] theorem val_one : (1 : InternalNatural V).val = (1 : V) := rfl
@[simp] theorem val_add (a b : InternalNatural V) :
    (a + b).val = ordinalAdd a.val b.val := rfl
@[simp] theorem val_mul (a b : InternalNatural V) :
    (a * b).val = naturalMul a.val b.val := rfl
@[simp] theorem val_natCast (n : ℕ) : (n : InternalNatural V).val = (n : V) := rfl

instance (n : InternalNatural V) : IsOrdinal n.val := IsOrdinal.of_mem n.property

instance : LT (InternalNatural V) := ⟨fun a b ↦ a.val ∈ b.val⟩
instance : LE (InternalNatural V) := ⟨fun a b ↦ a.val ⊆ b.val⟩

@[simp] theorem lt_iff_mem (a b : InternalNatural V) : a < b ↔ a.val ∈ b.val := Iff.rfl
@[simp] theorem le_iff_subset (a b : InternalNatural V) : a ≤ b ↔ a.val ⊆ b.val := Iff.rfl

noncomputable instance : LinearOrder (InternalNatural V) where
  le_refl a := subset_refl a.val
  le_trans _ _ _ := subset_trans
  lt_iff_le_not_ge _ _ := IsOrdinal.mem_iff_subset_and_not_subset
  le_antisymm _ _ hab hba := Subtype.ext (subset_antisymm hab hba)
  le_total a b := IsOrdinal.subset_or_supset a.val b.val
  toDecidableLE := Classical.decRel LE.le

theorem nonneg (a : InternalNatural V) : 0 ≤ a := empty_subset _

theorem pos_iff_ne_zero (a : InternalNatural V) : 0 < a ↔ a ≠ 0 :=
  (lt_iff_le_and_ne).trans (by simp [nonneg a, ne_comm])

instance : Nontrivial (InternalNatural V) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hv : (0 : V) = (1 : V) := congrArg Subtype.val h
  have hm : (0 : V) ∈ (1 : V) := by simp
  rw [hv] at hm
  exact mem_irrefl _ hm

instance : IsStrictOrderedRing (InternalNatural V) where
  add_le_add_left a b hab c := ordinalAdd_mono_first_natural a.property b.property c.property hab
  le_of_add_le_add_left a b c h := by
    by_contra hbc
    have hcb : c.val ∈ b.val := (lt_of_not_ge hbc : c < b)
    have ht : ordinalAdd a.val c.val ∈ ordinalAdd a.val b.val := ordinalAdd_mem hcb
    exact mem_irrefl _ (h _ ht)
  zero_le_one := empty_subset _
  mul_lt_mul_of_pos_left a ha b c hbc := by
    change naturalMul a.val b.val ∈ naturalMul a.val c.val
    rw [naturalMul_comm a.property b.property, naturalMul_comm a.property c.property]
    exact naturalMul_lt_first b.property c.property a.property hbc ha
  mul_lt_mul_of_pos_right c hc a b hab :=
    naturalMul_lt_first a.property b.property c.property hab hc

theorem cancel_add_left {a b c : InternalNatural V} (h : a + b = a + c) : b = c := by
  let := IsOrdinal.of_mem b.property
  let := IsOrdinal.of_mem c.property
  exact Subtype.ext (ordinalAdd_right_injective (congrArg Subtype.val h))

theorem cancel_mul_right {a b c : InternalNatural V} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  let := IsOrdinal.of_mem a.property
  let := IsOrdinal.of_mem b.property
  have hc0 : (0 : V) ∈ c.val := by
    rcases internalNatural_cases c.property with he | ⟨n, hn, he⟩
    · exact False.elim (hc (Subtype.ext he))
    · rw [he]
      exact zero_mem_succ_natural hn
  have hv := congrArg Subtype.val h
  change naturalMul a.val c.val = naturalMul b.val c.val at hv
  rcases IsOrdinal.mem_trichotomy a.val b.val with hlt | he | hgt
  · have hh := naturalMul_lt_first a.property b.property c.property hlt hc0
    rw [hv] at hh
    exact False.elim (mem_irrefl _ hh)
  · exact Subtype.ext he
  · have hh := naturalMul_lt_first b.property a.property c.property hgt hc0
    rw [hv] at hh
    exact False.elim (mem_irrefl _ hh)

theorem mul_eq_zero_cases {a b : InternalNatural V} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases hb : b = 0
  · exact Or.inr hb
  · exact Or.inl (cancel_mul_right hb (by simpa only [zero_mul] using h))

end InternalNatural

end ZFVP
