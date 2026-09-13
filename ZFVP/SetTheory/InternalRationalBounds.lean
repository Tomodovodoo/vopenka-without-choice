import ZFVP.SetTheory.InternalRationalField
import Mathlib.Algebra.Order.Field.Basic

/-! Rational bounds by elements of the model's whole omega. These statements
do not assert external Archimedeanness of a nonstandard model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace InternalNatural

theorem one_le_of_pos {n : InternalNatural V} (hn : 0 < n) : 1 ≤ n := by
  change (1 : V) ⊆ n.val
  intro z hz
  have he : z = (0 : V) := by simpa only [one_def, mem_singleton_iff] using hz
  exact he ▸ hn

end InternalNatural

namespace InternalRational

noncomputable def ofRep (r : InternalRationalRep V) : InternalRational V :=
  ⟨rationalClass r.code, rationalClass_mem_internalRationals r.code_mem⟩

theorem ofNatural_le_iff (a b : InternalNatural V) : ofNatural a ≤ ofNatural b ↔ a ≤ b := by
  rw [← not_lt, ofNatural_lt_iff, not_lt]

theorem ofNatural_nonneg (n : InternalNatural V) : 0 ≤ ofNatural n := by
  simpa only [ofNatural_zero] using (ofNatural_le_iff 0 n).mpr (InternalNatural.nonneg n)

theorem ofNatural_pos_iff (n : InternalNatural V) : 0 < ofNatural n ↔ 0 < n := by
  simpa only [ofNatural_zero] using ofNatural_lt_iff (0 : InternalNatural V) n

theorem ofRep_mul_den (r : InternalRationalRep V) :
    ofRep r * ofNatural r.den = ofNatural r.pos - ofNatural r.neg := by
  rw [sub_eq_add_neg]
  apply Subtype.ext
  change rationalMul (rationalClass r.code) (rationalNatural r.den.val) =
    rationalAdd (rationalNatural r.pos.val) (rationalNeg (rationalNatural r.neg.val))
  rw [rationalNatural_rep, rationalNatural_rep, rationalNatural_rep,
    rationalMul_reps, rationalNeg_rep, rationalAdd_reps]
  apply rationalClass_eq_of_reps_equal
  dsimp [InternalRationalRep.Equal, InternalRationalRep.mul, InternalRationalRep.add,
    InternalRationalRep.negation, InternalRationalRep.natural]
  ring

theorem ofRep_eq_fraction (r : InternalRationalRep V) :
    ofRep r = (ofNatural r.pos - ofNatural r.neg) / ofNatural r.den :=
  (eq_div_iff (ne_of_gt ((ofNatural_pos_iff r.den).mpr r.den_pos))).mpr (ofRep_mul_den r)

theorem ofRep_le_numerator (r : InternalRationalRep V) : ofRep r ≤ ofNatural r.pos := by
  rw [ofRep_eq_fraction]
  apply (div_le_iff₀ ((ofNatural_pos_iff r.den).mpr r.den_pos)).mpr
  have hden : (1 : InternalRational V) ≤ ofNatural r.den := by
    simpa only [ofNatural_one] using
      (ofNatural_le_iff 1 r.den).mpr (InternalNatural.one_le_of_pos r.den_pos)
  have hmul : ofNatural r.pos ≤ ofNatural r.pos * ofNatural r.den := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hden (ofNatural_nonneg r.pos)
  exact le_trans (sub_le_self _ (ofNatural_nonneg r.neg)) hmul

theorem exists_natural_gt (q : InternalRational V) :
    ∃ n : InternalNatural V, q < ofNatural n := by
  obtain ⟨r, hr⟩ := internalRational_exists_rep q.property
  have he : q = ofRep r := Subtype.ext hr
  refine ⟨r.pos + 1, ?_⟩
  rw [he, ofNatural_add, ofNatural_one]
  exact lt_of_le_of_lt (ofRep_le_numerator r) (lt_add_one _)

theorem exists_negative_natural_lt (q : InternalRational V) :
    ∃ n : InternalNatural V, -ofNatural n < q := by
  obtain ⟨n, hn⟩ := exists_natural_gt (-q)
  exact ⟨n, by simpa only [neg_neg] using neg_lt_neg hn⟩

theorem exists_small_natural_inverse {q : InternalRational V} (hq : 0 < q) :
    ∃ n : InternalNatural V, 0 < n ∧ (ofNatural n)⁻¹ < q := by
  obtain ⟨n, hn⟩ := exists_natural_gt q⁻¹
  have hni : 0 < ofNatural n := lt_trans (inv_pos.mpr hq) hn
  refine ⟨n, (ofNatural_pos_iff n).mp hni, ?_⟩
  simpa only [inv_inv] using (inv_lt_inv₀ hni (inv_pos.mpr hq)).mpr hn

end InternalRational

theorem rational_bounded_above_by_natural {q : V} (hq : q ∈ internalRationals V) :
    ∃ n ∈ (ω : V), InternalRationalLT q (rationalNatural n) := by
  obtain ⟨n, hn⟩ := InternalRational.exists_natural_gt (⟨q, hq⟩ : InternalRational V)
  exact ⟨n.val, n.property, hn⟩

theorem rational_bounded_below_by_negative_natural {q : V} (hq : q ∈ internalRationals V) :
    ∃ n ∈ (ω : V), InternalRationalLT (rationalNeg (rationalNatural n)) q := by
  obtain ⟨n, hn⟩ := InternalRational.exists_negative_natural_lt (⟨q, hq⟩ : InternalRational V)
  exact ⟨n.val, n.property, hn⟩

theorem rational_small_inverse {q : V} (hq : q ∈ internalRationals V)
    (hqpos : InternalRationalLT (rationalZero V) q) :
    ∃ n ∈ (ω : V), (0 : V) ∈ n ∧ InternalRationalLT (rationalInv (rationalNatural n)) q := by
  obtain ⟨n, hn, hlt⟩ := InternalRational.exists_small_natural_inverse
    (q := (⟨q, hq⟩ : InternalRational V)) hqpos
  exact ⟨n.val, n.property, hn, hlt⟩

end ZFVP
