import ZFVP.SetTheory.InternalRationalArithmetic

/-! An ordered-ring interface to the actual internal rational quotient.
All values still range over that quotient. Lean Nat and Int casts below are
metatheoretic algebraic bookkeeping, not a restriction on the model's numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalNaturalFormula : SetTheorySemisentence 2 :=
  f“q n. q = !rationalClassFormula
    (!kpair.dfn (!kpair.dfn n (!isEmpty)) (!succ.dfn (!isEmpty)))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalNatural (n : V) : V := rationalClass ⟨⟨n, 0⟩ₖ, 1⟩ₖ

instance rationalNaturalFormula_defined :
    ℒₛₑₜ-function₁[V] rationalNatural via rationalNaturalFormula :=
  ⟨fun v ↦ by simp [rationalNaturalFormula, rationalNatural, zero_def]; rfl⟩

instance rationalNatural_definable : ℒₛₑₜ-function₁[V] rationalNatural :=
  rationalNaturalFormula_defined.to_definable

namespace InternalRationalRep

noncomputable def natural (n : InternalNatural V) : InternalRationalRep V := ⟨n, 0, 1, zero_lt_one⟩

end InternalRationalRep

theorem rationalNatural_rep (n : InternalNatural V) :
    rationalNatural n.val = rationalClass (InternalRationalRep.natural n).code := rfl

theorem rationalNatural_mem {n : V} (hn : n ∈ (ω : V)) :
    rationalNatural n ∈ internalRationals V :=
  rationalClass_mem_internalRationals (InternalRationalRep.natural ⟨n, hn⟩).code_mem

theorem rationalNatural_zero : rationalNatural (0 : V) = rationalZero V := rfl
theorem rationalNatural_one : rationalNatural (1 : V) = rationalOne V := rfl

theorem rationalNatural_add {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) :
    rationalNatural (ordinalAdd n m) = rationalAdd (rationalNatural n) (rationalNatural m) := by
  let a : InternalNatural V := ⟨n, hn⟩
  let b : InternalNatural V := ⟨m, hm⟩
  change rationalNatural (a + b).val = rationalAdd (rationalNatural a.val) (rationalNatural b.val)
  rw [rationalNatural_rep, rationalNatural_rep, rationalNatural_rep, rationalAdd_reps]
  apply rationalClass_eq_of_reps_equal
  dsimp [InternalRationalRep.Equal, InternalRationalRep.natural, InternalRationalRep.add]
  ring

theorem rationalNatural_mul {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) :
    rationalNatural (naturalMul n m) = rationalMul (rationalNatural n) (rationalNatural m) := by
  let a : InternalNatural V := ⟨n, hn⟩
  let b : InternalNatural V := ⟨m, hm⟩
  change rationalNatural (a * b).val = rationalMul (rationalNatural a.val) (rationalNatural b.val)
  rw [rationalNatural_rep, rationalNatural_rep, rationalNatural_rep, rationalMul_reps]
  apply rationalClass_eq_of_reps_equal
  dsimp [InternalRationalRep.Equal, InternalRationalRep.natural, InternalRationalRep.mul]
  ring

namespace InternalNatural

theorem exists_pos_add_of_lt {a b : InternalNatural V} (hab : a < b) :
    ∃ d : InternalNatural V, 0 < d ∧ a + d = b := by
  obtain ⟨d, hd, had⟩ := ordinalAdd_difference_natural a.property b.property
    ((le_iff_subset a b).mp (le_of_lt hab))
  refine ⟨⟨d, hd⟩, ?_, Subtype.ext had⟩
  apply (pos_iff_ne_zero _).mpr
  intro h
  have h' : a + (0 : InternalNatural V) = b := h ▸ (Subtype.ext had : a + ⟨d, hd⟩ = b)
  have he : a = b := by simpa only [add_zero] using h'
  exact (ne_of_lt hab) he

theorem skew_mul_lt {a b n p : InternalNatural V} (hab : a < b) (hnp : n < p) :
    a * p + b * n < a * n + b * p := by
  obtain ⟨d, hd, had⟩ := exists_pos_add_of_lt hab
  obtain ⟨e, he, hne⟩ := exists_pos_add_of_lt hnp
  calc
    a * p + b * n = a * n + a * n + a * e + d * n := by rw [← had, ← hne]; ring
    _ < a * n + a * n + a * e + d * n + d * e :=
      lt_add_of_pos_right _ (mul_pos hd he)
    _ = a * n + b * p := by rw [← had, ← hne]; ring

end InternalNatural

namespace InternalRationalRep

theorem less_add_right {r s : InternalRationalRep V} (h : r.Less s) (t : InternalRationalRep V) :
    (r.add t).Less (s.add t) := by
  dsimp [Less] at h
  dsimp [Less, add]
  calc
    (r.pos * t.den + t.pos * r.den) * (s.den * t.den) +
        (s.neg * t.den + t.neg * s.den) * (r.den * t.den) =
        (t.pos + t.neg) * r.den * s.den * t.den +
          (r.pos * s.den + s.neg * r.den) * (t.den * t.den) := by ring
    _ < (t.pos + t.neg) * r.den * s.den * t.den +
          (r.neg * s.den + s.pos * r.den) * (t.den * t.den) :=
      add_lt_add_right (mul_lt_mul_of_pos_right h (mul_pos t.den_pos t.den_pos)) _
    _ = (r.neg * t.den + t.neg * r.den) * (s.den * t.den) +
          (s.pos * t.den + t.pos * s.den) * (r.den * t.den) := by ring

theorem less_mul_pos_right {r s t : InternalRationalRep V} (h : r.Less s)
    (ht : zero.Less t) : (r.mul t).Less (s.mul t) := by
  have ht' : t.neg < t.pos := by simpa [Less, zero] using ht
  have hh := InternalNatural.skew_mul_lt h ht'
  dsimp [Less, mul]
  calc
    (r.pos * t.pos + r.neg * t.neg) * (s.den * t.den) +
        (s.pos * t.neg + s.neg * t.pos) * (r.den * t.den) =
        ((r.pos * s.den + s.neg * r.den) * t.pos +
          (r.neg * s.den + s.pos * r.den) * t.neg) * t.den := by ring
    _ < ((r.pos * s.den + s.neg * r.den) * t.neg +
          (r.neg * s.den + s.pos * r.den) * t.pos) * t.den :=
      mul_lt_mul_of_pos_right hh t.den_pos
    _ = (r.pos * t.neg + r.neg * t.pos) * (s.den * t.den) +
          (s.pos * t.pos + s.neg * t.neg) * (r.den * t.den) := by ring

end InternalRationalRep

theorem rationalAdd_lt_right {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V) (hqr : InternalRationalLT q r) :
    InternalRationalLT (rationalAdd q s) (rationalAdd r s) := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  rw [internalRationalLT_reps_iff] at hqr
  simp only [rationalAdd_reps, internalRationalLT_reps_iff]
  exact InternalRationalRep.less_add_right hqr c

theorem rationalMul_lt_pos_right {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V)
    (hqr : InternalRationalLT q r) (hspos : InternalRationalLT (rationalZero V) s) :
    InternalRationalLT (rationalMul q s) (rationalMul r s) := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  rw [internalRationalLT_reps_iff] at hqr
  rw [rationalZero_eq, internalRationalLT_reps_iff] at hspos
  simp only [rationalMul_reps, internalRationalLT_reps_iff]
  exact InternalRationalRep.less_mul_pos_right hqr hspos

abbrev InternalRational (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] := {q : V // q ∈ internalRationals V}

namespace InternalRational

noncomputable instance : Zero (InternalRational V) := ⟨⟨rationalZero V, rationalZero_mem⟩⟩
noncomputable instance : One (InternalRational V) := ⟨⟨rationalOne V, rationalOne_mem⟩⟩
noncomputable instance : Add (InternalRational V) :=
  ⟨fun a b ↦ ⟨rationalAdd a.val b.val, rationalAdd_mem a.property b.property⟩⟩
noncomputable instance : Mul (InternalRational V) :=
  ⟨fun a b ↦ ⟨rationalMul a.val b.val, rationalMul_mem a.property b.property⟩⟩
noncomputable instance : Neg (InternalRational V) :=
  ⟨fun a ↦ ⟨rationalNeg a.val, rationalNeg_mem a.property⟩⟩

noncomputable instance : CommRing (InternalRational V) where
  add_assoc a b c := Subtype.ext (rationalAdd_assoc a.property b.property c.property)
  zero_add a := Subtype.ext (by
    change rationalAdd (rationalZero V) a.val = a.val
    rw [rationalAdd_comm rationalZero_mem a.property]
    exact rationalAdd_zero a.property)
  add_zero a := Subtype.ext (rationalAdd_zero a.property)
  add_comm a b := Subtype.ext (rationalAdd_comm a.property b.property)
  neg_add_cancel a := Subtype.ext (by
    change rationalAdd (rationalNeg a.val) a.val = rationalZero V
    rw [rationalAdd_comm (rationalNeg_mem a.property) a.property]
    exact rationalAdd_neg a.property)
  mul_assoc a b c := Subtype.ext (rationalMul_assoc a.property b.property c.property)
  one_mul a := Subtype.ext (by
    change rationalMul (rationalOne V) a.val = a.val
    rw [rationalMul_comm rationalOne_mem a.property]
    exact rationalMul_one a.property)
  mul_one a := Subtype.ext (rationalMul_one a.property)
  mul_comm a b := Subtype.ext (rationalMul_comm a.property b.property)
  zero_mul a := Subtype.ext (by
    change rationalMul (rationalZero V) a.val = rationalZero V
    rw [rationalMul_comm rationalZero_mem a.property]
    exact rationalMul_zero a.property)
  mul_zero a := Subtype.ext (rationalMul_zero a.property)
  left_distrib a b c := Subtype.ext (rationalMul_add a.property b.property c.property)
  right_distrib a b c := Subtype.ext (by
    change rationalMul (rationalAdd a.val b.val) c.val =
      rationalAdd (rationalMul a.val c.val) (rationalMul b.val c.val)
    rw [rationalMul_comm (rationalAdd_mem a.property b.property) c.property,
      rationalMul_add c.property a.property b.property,
      rationalMul_comm c.property a.property, rationalMul_comm c.property b.property])
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  natCast n := ⟨rationalNatural (n : V), rationalNatural_mem (by simp)⟩
  natCast_zero := rfl
  natCast_succ n := by
    apply Subtype.ext
    change rationalNatural ((n + 1 : ℕ) : V) = rationalAdd (rationalNatural (n : V)) (rationalOne V)
    rw [num_succ_def, ← ordinalAdd_one_natural (show (n : V) ∈ ω by simp),
      rationalNatural_add (by simp) (by simp), rationalNatural_one]

@[simp] theorem val_zero : (0 : InternalRational V).val = rationalZero V := rfl
@[simp] theorem val_one : (1 : InternalRational V).val = rationalOne V := rfl
@[simp] theorem val_add (a b : InternalRational V) : (a + b).val = rationalAdd a.val b.val := rfl
@[simp] theorem val_mul (a b : InternalRational V) : (a * b).val = rationalMul a.val b.val := rfl
@[simp] theorem val_neg (a : InternalRational V) : (-a).val = rationalNeg a.val := rfl
@[simp] theorem val_natCast (n : ℕ) : (n : InternalRational V).val = rationalNatural (n : V) := rfl

instance : Nontrivial (InternalRational V) :=
  ⟨⟨0, 1, fun h ↦ rationalZero_ne_one (V := V) (congrArg Subtype.val h)⟩⟩

instance : LT (InternalRational V) := ⟨fun a b ↦ InternalRationalLT a.val b.val⟩
instance : LE (InternalRational V) := ⟨fun a b ↦ ¬ InternalRationalLT b.val a.val⟩

@[simp] theorem lt_iff (a b : InternalRational V) : a < b ↔ InternalRationalLT a.val b.val := Iff.rfl
theorem le_iff (a b : InternalRational V) : a ≤ b ↔ ¬ InternalRationalLT b.val a.val := Iff.rfl

noncomputable instance : LinearOrder (InternalRational V) where
  le_refl a := internalRationalLT_irrefl a.property
  le_trans a b c hab hbc hca := by
    rcases internalRational_trichotomy a.property b.property with hab' | he | hba
    · exact hbc (internalRationalLT_trans c.property a.property b.property hca hab')
    · exact hbc (he ▸ hca)
    · exact hab hba
  le_antisymm a b hab hba := by
    rcases internalRational_trichotomy a.property b.property with hab' | he | hba'
    · exact (hba hab').elim
    · exact Subtype.ext he
    · exact (hab hba').elim
  lt_iff_le_not_ge a b := by
    change InternalRationalLT a.val b.val ↔
      ¬ InternalRationalLT b.val a.val ∧ ¬¬ InternalRationalLT a.val b.val
    constructor
    · intro h
      exact ⟨fun h' ↦ internalRationalLT_irrefl a.property
        (internalRationalLT_trans a.property b.property a.property h h'), not_not.mpr h⟩
    · exact fun h ↦ not_not.mp h.2
  le_total a b := by
    by_cases hba : InternalRationalLT b.val a.val
    · exact Or.inr (fun hab ↦ internalRationalLT_irrefl a.property
        (internalRationalLT_trans a.property b.property a.property hab hba))
    · exact Or.inl hba
  toDecidableLE := Classical.decRel LE.le

instance : IsStrictOrderedRing (InternalRational V) where
  add_le_add_left a b hab c := by
    intro h
    rcases lt_or_eq_of_le hab with hlt | he
    · have h' := rationalAdd_lt_right a.property b.property c.property hlt
      exact internalRationalLT_irrefl (rationalAdd_mem a.property c.property)
        (internalRationalLT_trans (rationalAdd_mem a.property c.property)
          (rationalAdd_mem b.property c.property) (rationalAdd_mem a.property c.property) h' h)
    · have he' : a + c = b + c := congrArg (fun x ↦ x + c) he
      have h' : b + c < a + c := h
      rw [he'] at h'
      exact lt_irrefl _ h'
  le_of_add_le_add_left a b c h := by
    intro hcb
    have hh := rationalAdd_lt_right c.property b.property a.property hcb
    rw [← rationalAdd_comm a.property c.property, ← rationalAdd_comm a.property b.property] at hh
    exact h hh
  zero_le_one := by
    change ¬ InternalRationalLT (rationalOne V) (rationalZero V)
    rw [rationalOne_eq, rationalZero_eq, internalRationalLT_reps_iff]
    simp [InternalRationalRep.Less, InternalRationalRep.one, InternalRationalRep.zero, zero_def]
  mul_lt_mul_of_pos_left a ha b c hbc := by
    change InternalRationalLT (rationalMul a.val b.val) (rationalMul a.val c.val)
    rw [rationalMul_comm a.property b.property, rationalMul_comm a.property c.property]
    exact rationalMul_lt_pos_right b.property c.property a.property hbc ha
  mul_lt_mul_of_pos_right c hc a b hab :=
    rationalMul_lt_pos_right a.property b.property c.property hab hc

noncomputable def ofNatural (n : InternalNatural V) : InternalRational V :=
  ⟨rationalNatural n.val, rationalNatural_mem n.property⟩

@[simp] theorem ofNatural_zero : ofNatural (0 : InternalNatural V) = 0 := rfl
@[simp] theorem ofNatural_one : ofNatural (1 : InternalNatural V) = 1 := rfl
@[simp] theorem ofNatural_add (a b : InternalNatural V) : ofNatural (a + b) = ofNatural a + ofNatural b :=
  Subtype.ext (rationalNatural_add a.property b.property)
@[simp] theorem ofNatural_mul (a b : InternalNatural V) : ofNatural (a * b) = ofNatural a * ofNatural b :=
  Subtype.ext (rationalNatural_mul a.property b.property)

theorem ofNatural_lt_iff (a b : InternalNatural V) : ofNatural a < ofNatural b ↔ a < b := by
  change InternalRationalLT (rationalNatural a.val) (rationalNatural b.val) ↔ a < b
  rw [rationalNatural_rep, rationalNatural_rep, internalRationalLT_reps_iff]
  simp [InternalRationalRep.Less, InternalRationalRep.natural]

theorem ofNatural_injective : Function.Injective (ofNatural (V := V)) := by
  intro a b h
  rcases lt_trichotomy a b with hab | he | hba
  · have h' := (ofNatural_lt_iff a b).mpr hab
    rw [h] at h'
    exact (lt_irrefl _ h').elim
  · exact he
  · have h' := (ofNatural_lt_iff b a).mpr hba
    rw [h] at h'
    exact (lt_irrefl _ h').elim

end InternalRational

end ZFVP
