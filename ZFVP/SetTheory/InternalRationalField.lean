import ZFVP.SetTheory.InternalRationalRing
import Mathlib.Algebra.Field.Defs

/-! Reciprocal as an internal set, with a proof of the ordered-field laws.
The reciprocal is assembled from its uniquely determined fraction class;
no representative-selection function or internal Choice is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalInvFormula : SetTheorySemisentence 2 :=
  f“z q. ∀ x, x ∈ z ↔ x ∈ !rationalCodeSpaceFormula ∧
    ((q = !rationalZeroFormula ∧ x ∈ !rationalZeroFormula) ∨
      ∃ r ∈ !internalRationalsFormula, !rationalMulFormula q r = !rationalOneFormula ∧ x ∈ r)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalRational_subset_codes {q : V} (hq : q ∈ internalRationals V) :
    q ⊆ rationalCodeSpace V := by
  obtain ⟨c, _, rfl⟩ := (mem_internalRationals_iff q).mp hq
  exact fun x hx ↦ ((mem_rationalClass_iff c x).mp hx).1

theorem rational_exists_inverse {q : V} (hq : q ∈ internalRationals V) (hqn : q ≠ rationalZero V) :
    ∃ r ∈ internalRationals V, rationalMul q r = rationalOne V := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  rcases lt_trichotomy a.pos a.neg with hlt | he | hgt
  · obtain ⟨d, hd, had⟩ := InternalNatural.exists_pos_add_of_lt hlt
    let b : InternalRationalRep V := ⟨0, a.den, d, hd⟩
    refine ⟨rationalClass b.code, rationalClass_mem_internalRationals b.code_mem, ?_⟩
    rw [rationalMul_reps, rationalOne_eq]
    apply rationalClass_eq_of_reps_equal
    dsimp [InternalRationalRep.Equal, InternalRationalRep.mul, InternalRationalRep.one, b]
    rw [← had]
    ring
  · apply False.elim
    apply hqn
    rw [rationalZero_eq]
    apply rationalClass_eq_of_reps_equal
    simp [InternalRationalRep.Equal, InternalRationalRep.zero, he]
  · obtain ⟨d, hd, had⟩ := InternalNatural.exists_pos_add_of_lt hgt
    let b : InternalRationalRep V := ⟨a.den, 0, d, hd⟩
    refine ⟨rationalClass b.code, rationalClass_mem_internalRationals b.code_mem, ?_⟩
    rw [rationalMul_reps, rationalOne_eq]
    apply rationalClass_eq_of_reps_equal
    dsimp [InternalRationalRep.Equal, InternalRationalRep.mul, InternalRationalRep.one, b]
    rw [← had]
    ring

theorem rational_inverse_unique {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V)
    (hqr : rationalMul q r = rationalOne V) (hqs : rationalMul q s = rationalOne V) : r = s := by
  let a : InternalRational V := ⟨q, hq⟩
  let b : InternalRational V := ⟨r, hr⟩
  let c : InternalRational V := ⟨s, hs⟩
  have hab : a * b = 1 := Subtype.ext hqr
  have hac : a * c = 1 := Subtype.ext hqs
  have hbc : b = c := calc
    b = b * 1 := (mul_one b).symm
    _ = b * (a * c) := by rw [hac]
    _ = (b * a) * c := (mul_assoc b a c).symm
    _ = (a * b) * c := by rw [mul_comm b a]
    _ = c := by rw [hab, one_mul]
  exact congrArg Subtype.val hbc

noncomputable def rationalInv (q : V) : V :=
  {x ∈ rationalCodeSpace V ; (q = rationalZero V ∧ x ∈ rationalZero V) ∨
    ∃ r ∈ internalRationals V, rationalMul q r = rationalOne V ∧ x ∈ r}

instance rationalInvFormula_defined : ℒₛₑₜ-function₁[V] rationalInv via rationalInvFormula :=
  ⟨fun v ↦ by
    change rationalInvFormula.Evalb v ↔ v 0 = rationalInv (v 1)
    rw [mem_ext_iff]
    simp [rationalInvFormula, rationalInv]⟩

instance rationalInv_definable : ℒₛₑₜ-function₁[V] rationalInv := rationalInvFormula_defined.to_definable

theorem rationalInv_zero : rationalInv (rationalZero V) = rationalZero V := by
  apply mem_ext
  intro x
  simp only [rationalInv, mem_sep_iff, true_and]
  constructor
  · rintro ⟨_, hx | ⟨r, hr, hzr, _⟩⟩
    · exact hx
    · rw [rationalMul_comm rationalZero_mem hr, rationalMul_zero hr] at hzr
      exact (rationalZero_ne_one hzr).elim
  · intro hx
    exact ⟨internalRational_subset_codes rationalZero_mem x hx, Or.inl hx⟩

theorem rationalInv_eq_of_mul_eq_one {q r : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hqr : rationalMul q r = rationalOne V) : rationalInv q = r := by
  have hqn : q ≠ rationalZero V := by
    intro h
    rw [h, rationalMul_comm rationalZero_mem hr, rationalMul_zero hr] at hqr
    exact rationalZero_ne_one hqr
  apply mem_ext
  intro x
  simp only [rationalInv, mem_sep_iff]
  constructor
  · rintro ⟨_, ⟨hqz, _⟩ | ⟨s, hs, hqs, hxs⟩⟩
    · exact (hqn hqz).elim
    · exact (rational_inverse_unique hq hs hr hqs hqr) ▸ hxs
  · intro hxr
    exact ⟨internalRational_subset_codes hr x hxr, Or.inr ⟨r, hr, hqr, hxr⟩⟩

theorem rationalInv_mem {q : V} (hq : q ∈ internalRationals V) :
    rationalInv q ∈ internalRationals V := by
  by_cases hqn : q = rationalZero V
  · rw [hqn, rationalInv_zero]
    exact rationalZero_mem
  · obtain ⟨r, hr, hqr⟩ := rational_exists_inverse hq hqn
    rw [rationalInv_eq_of_mul_eq_one hq hr hqr]
    exact hr

theorem rationalMul_inv {q : V} (hq : q ∈ internalRationals V) (hqn : q ≠ rationalZero V) :
    rationalMul q (rationalInv q) = rationalOne V := by
  obtain ⟨r, hr, hqr⟩ := rational_exists_inverse hq hqn
  rw [rationalInv_eq_of_mul_eq_one hq hr hqr]
  exact hqr

namespace InternalRational

noncomputable instance : Inv (InternalRational V) :=
  ⟨fun a ↦ ⟨rationalInv a.val, rationalInv_mem a.property⟩⟩

noncomputable instance : Field (InternalRational V) where
  inv_zero := Subtype.ext rationalInv_zero
  mul_inv_cancel a ha := Subtype.ext (rationalMul_inv a.property (fun h ↦ ha (Subtype.ext h)))
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

@[simp] theorem val_inv (a : InternalRational V) : (a⁻¹).val = rationalInv a.val := rfl

end InternalRational

end ZFVP
