import ZFVP.SetTheory.InternalRationalCodes

/-! The dense linear order of the internally constructed rational quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalCodeLTFormula : SetTheorySemisentence 2 :=
  f“c e. !ordinalAddFormula
      (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
      (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c)) ∈
    !ordinalAddFormula
      (!naturalMulFormula (!kpair.π₂.dfn (!kpair.π₁.dfn c)) (!kpair.π₂.dfn e))
      (!naturalMulFormula (!kpair.π₁.dfn (!kpair.π₁.dfn e)) (!kpair.π₂.dfn c))”

def internalRationalLTFormula : SetTheorySemisentence 2 :=
  f“q r. ∃ c ∈ q, ∃ e ∈ r, !rationalCodeLTFormula c e”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RationalCodeLT (c e : V) : Prop :=
  ordinalAdd (naturalMul (kpair.π₁ (kpair.π₁ c)) (kpair.π₂ e))
      (naturalMul (kpair.π₂ (kpair.π₁ e)) (kpair.π₂ c)) ∈
    ordinalAdd (naturalMul (kpair.π₂ (kpair.π₁ c)) (kpair.π₂ e))
      (naturalMul (kpair.π₁ (kpair.π₁ e)) (kpair.π₂ c))

instance rationalCodeLTFormula_defined :
    ℒₛₑₜ-relation[V] RationalCodeLT via rationalCodeLTFormula :=
  ⟨fun v ↦ by simp [rationalCodeLTFormula, RationalCodeLT]⟩

instance rationalCodeLT_definable : ℒₛₑₜ-relation[V] RationalCodeLT :=
  rationalCodeLTFormula_defined.to_definable

/-- A finite algebraic interface to an actual internal fraction code. -/
structure InternalRationalRep (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] where
  pos : InternalNatural V
  neg : InternalNatural V
  den : InternalNatural V
  den_pos : 0 < den

namespace InternalRationalRep

noncomputable def code (r : InternalRationalRep V) : V :=
  ⟨⟨r.pos.val, r.neg.val⟩ₖ, r.den.val⟩ₖ

theorem code_mem (r : InternalRationalRep V) : r.code ∈ rationalCodeSpace V := by
  apply (mem_rationalCodeSpace_iff _).mpr
  refine ⟨r.pos.val, r.pos.property, r.neg.val, r.neg.property,
    r.den.val, r.den.property, ?_, rfl⟩
  intro h
  exact (ne_of_gt r.den_pos) (Subtype.ext h)

def Equal (r s : InternalRationalRep V) : Prop :=
  r.pos * s.den + s.neg * r.den = r.neg * s.den + s.pos * r.den

def Less (r s : InternalRationalRep V) : Prop :=
  r.pos * s.den + s.neg * r.den < r.neg * s.den + s.pos * r.den

theorem equiv_code_iff (r s : InternalRationalRep V) :
    RationalCodeEquiv r.code s.code ↔ r.Equal s := by
  simp only [RationalCodeEquiv, code, kpair.π₁_kpair, kpair.π₂_kpair, Equal]
  constructor
  · exact fun h ↦ Subtype.ext h
  · exact fun h ↦ congrArg Subtype.val h

theorem lt_code_iff (r s : InternalRationalRep V) :
    RationalCodeLT r.code s.code ↔ r.Less s := by
  simp only [RationalCodeLT, code, kpair.π₁_kpair, kpair.π₂_kpair, Less,
    InternalNatural.lt_iff_mem, InternalNatural.val_add, InternalNatural.val_mul]

theorem equal_refl (r : InternalRationalRep V) : r.Equal r := add_comm _ _

theorem equal_symm {r s : InternalRationalRep V} (h : r.Equal s) : s.Equal r := by
  dsimp [Equal] at h ⊢
  simpa only [add_comm] using h.symm

theorem equal_trans {r s t : InternalRationalRep V} (h₁ : r.Equal s)
    (h₂ : s.Equal t) : r.Equal t :=
  InternalNatural.rational_balance_trans _ _ _ _ _ _ _ _ _ (ne_of_gt s.den_pos) h₁ h₂

theorem equal_less_trans {r s t : InternalRationalRep V} (h₁ : r.Equal s)
    (h₂ : s.Less t) : r.Less t := by
  dsimp [Equal] at h₁
  dsimp [Less] at h₂ ⊢
  apply (mul_lt_mul_iff_left₀ s.den_pos).mp
  apply lt_of_add_lt_add_left (a := s.neg * r.den * t.den + s.pos * r.den * t.den)
  calc
    s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.pos * t.den + t.neg * r.den) * s.den =
        (r.pos * s.den + s.neg * r.den) * t.den +
          (s.pos * t.den + t.neg * s.den) * r.den := by ring
    _ < (r.neg * s.den + s.pos * r.den) * t.den +
          (s.neg * t.den + t.pos * s.den) * r.den := by
      rw [h₁]
      exact add_lt_add_right (mul_lt_mul_of_pos_right h₂ r.den_pos) _
    _ = s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.neg * t.den + t.pos * r.den) * s.den := by ring

theorem less_equal_trans {r s t : InternalRationalRep V} (h₁ : r.Less s)
    (h₂ : s.Equal t) : r.Less t := by
  dsimp [Less] at h₁ ⊢
  dsimp [Equal] at h₂
  apply (mul_lt_mul_iff_left₀ s.den_pos).mp
  apply lt_of_add_lt_add_left (a := s.neg * r.den * t.den + s.pos * r.den * t.den)
  calc
    s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.pos * t.den + t.neg * r.den) * s.den =
        (r.pos * s.den + s.neg * r.den) * t.den +
          (s.pos * t.den + t.neg * s.den) * r.den := by ring
    _ < (r.neg * s.den + s.pos * r.den) * t.den +
          (s.neg * t.den + t.pos * s.den) * r.den := by
      rw [h₂]
      exact add_lt_add_left (mul_lt_mul_of_pos_right h₁ t.den_pos) _
    _ = s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.neg * t.den + t.pos * r.den) * s.den := by ring

theorem less_trans {r s t : InternalRationalRep V} (h₁ : r.Less s)
    (h₂ : s.Less t) : r.Less t := by
  dsimp [Less] at h₁ h₂ ⊢
  apply (mul_lt_mul_iff_left₀ s.den_pos).mp
  apply lt_of_add_lt_add_left (a := s.neg * r.den * t.den + s.pos * r.den * t.den)
  calc
    s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.pos * t.den + t.neg * r.den) * s.den =
        (r.pos * s.den + s.neg * r.den) * t.den +
          (s.pos * t.den + t.neg * s.den) * r.den := by ring
    _ < (r.neg * s.den + s.pos * r.den) * t.den +
          (s.neg * t.den + t.pos * s.den) * r.den :=
      add_lt_add (mul_lt_mul_of_pos_right h₁ t.den_pos)
        (mul_lt_mul_of_pos_right h₂ r.den_pos)
    _ = s.neg * r.den * t.den + s.pos * r.den * t.den +
        (r.neg * t.den + t.pos * r.den) * s.den := by ring

theorem less_irrefl (r : InternalRationalRep V) : ¬ r.Less r := by
  dsimp [Less]
  rw [add_comm (r.pos * r.den) (r.neg * r.den)]
  exact lt_irrefl _

theorem trichotomy (r s : InternalRationalRep V) : r.Less s ∨ r.Equal s ∨ s.Less r := by
  dsimp [Less, Equal]
  simpa only [add_comm] using
    lt_trichotomy (r.pos * s.den + s.neg * r.den) (r.neg * s.den + s.pos * r.den)

noncomputable def midpoint (r s : InternalRationalRep V) : InternalRationalRep V where
  pos := r.pos * s.den + s.pos * r.den
  neg := r.neg * s.den + s.neg * r.den
  den := r.den * s.den + r.den * s.den
  den_pos := add_pos (mul_pos r.den_pos s.den_pos) (mul_pos r.den_pos s.den_pos)

theorem less_midpoint {r s : InternalRationalRep V} (h : r.Less s) : r.Less (r.midpoint s) := by
  dsimp [Less] at h
  dsimp [Less, midpoint]
  calc
    r.pos * (r.den * s.den + r.den * s.den) +
        (r.neg * s.den + s.neg * r.den) * r.den =
        r.pos * r.den * s.den + r.neg * r.den * s.den +
          (r.pos * s.den + s.neg * r.den) * r.den := by ring
    _ < r.pos * r.den * s.den + r.neg * r.den * s.den +
          (r.neg * s.den + s.pos * r.den) * r.den :=
      add_lt_add_right (mul_lt_mul_of_pos_right h r.den_pos) _
    _ = r.neg * (r.den * s.den + r.den * s.den) +
          (r.pos * s.den + s.pos * r.den) * r.den := by ring

theorem midpoint_less {r s : InternalRationalRep V} (h : r.Less s) : (r.midpoint s).Less s := by
  dsimp [Less] at h
  dsimp [Less, midpoint]
  calc
    (r.pos * s.den + s.pos * r.den) * s.den +
        s.neg * (r.den * s.den + r.den * s.den) =
        s.pos * r.den * s.den + s.neg * r.den * s.den +
          (r.pos * s.den + s.neg * r.den) * s.den := by ring
    _ < s.pos * r.den * s.den + s.neg * r.den * s.den +
          (r.neg * s.den + s.pos * r.den) * s.den :=
      add_lt_add_right (mul_lt_mul_of_pos_right h s.den_pos) _
    _ = (r.neg * s.den + s.neg * r.den) * s.den +
          s.pos * (r.den * s.den + r.den * s.den) := by ring

noncomputable def next (r : InternalRationalRep V) : InternalRationalRep V where
  pos := r.pos + r.den
  neg := r.neg
  den := r.den
  den_pos := r.den_pos

noncomputable def previous (r : InternalRationalRep V) : InternalRationalRep V where
  pos := r.pos
  neg := r.neg + r.den
  den := r.den
  den_pos := r.den_pos

theorem less_next (r : InternalRationalRep V) : r.Less r.next := by
  dsimp [Less, next]
  calc
    r.pos * r.den + r.neg * r.den <
        r.pos * r.den + r.neg * r.den + r.den * r.den :=
      lt_add_of_pos_right _ (mul_pos r.den_pos r.den_pos)
    _ = r.neg * r.den + (r.pos + r.den) * r.den := by ring

theorem previous_less (r : InternalRationalRep V) : r.previous.Less r := by
  dsimp [Less, previous]
  calc
    r.pos * r.den + r.neg * r.den <
        r.pos * r.den + r.neg * r.den + r.den * r.den :=
      lt_add_of_pos_right _ (mul_pos r.den_pos r.den_pos)
    _ = (r.neg + r.den) * r.den + r.pos * r.den := by ring

end InternalRationalRep

theorem rationalCode_exists_rep {c : V} (hc : c ∈ rationalCodeSpace V) :
    ∃ r : InternalRationalRep V, c = r.code := by
  obtain ⟨a, ha, b, hb, d, hd, hdn, rfl⟩ := (mem_rationalCodeSpace_iff c).mp hc
  have hdp : (0 : InternalNatural V) < ⟨d, hd⟩ :=
    (InternalNatural.pos_iff_ne_zero _).mpr (fun h ↦ hdn (congrArg Subtype.val h))
  exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩, hdp⟩, rfl⟩

theorem rationalCodeLT_congr {c c' e e' : V}
    (hc : c ∈ rationalCodeSpace V) (hc' : c' ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) (he' : e' ∈ rationalCodeSpace V)
    (hcc : RationalCodeEquiv c c') (hee : RationalCodeEquiv e e') :
    RationalCodeLT c e ↔ RationalCodeLT c' e' := by
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  obtain ⟨r', rfl⟩ := rationalCode_exists_rep hc'
  obtain ⟨s, rfl⟩ := rationalCode_exists_rep he
  obtain ⟨s', rfl⟩ := rationalCode_exists_rep he'
  rw [InternalRationalRep.equiv_code_iff] at hcc hee
  rw [InternalRationalRep.lt_code_iff, InternalRationalRep.lt_code_iff]
  exact ⟨fun h ↦ InternalRationalRep.equal_less_trans (InternalRationalRep.equal_symm hcc)
      (InternalRationalRep.less_equal_trans h hee),
    fun h ↦ InternalRationalRep.equal_less_trans hcc
      (InternalRationalRep.less_equal_trans h (InternalRationalRep.equal_symm hee))⟩

def InternalRationalLT (q r : V) : Prop := ∃ c ∈ q, ∃ e ∈ r, RationalCodeLT c e

instance internalRationalLTFormula_defined :
    ℒₛₑₜ-relation[V] InternalRationalLT via internalRationalLTFormula :=
  ⟨fun v ↦ by simp [internalRationalLTFormula, InternalRationalLT]⟩

instance internalRationalLT_definable : ℒₛₑₜ-relation[V] InternalRationalLT :=
  internalRationalLTFormula_defined.to_definable

theorem internalRationalLT_classes_iff {c e : V} (hc : c ∈ rationalCodeSpace V)
    (he : e ∈ rationalCodeSpace V) :
    InternalRationalLT (rationalClass c) (rationalClass e) ↔ RationalCodeLT c e := by
  constructor
  · rintro ⟨c', hc', e', he', h⟩
    obtain ⟨hc'C, hcc'⟩ := (mem_rationalClass_iff c c').mp hc'
    obtain ⟨he'C, hee'⟩ := (mem_rationalClass_iff e e').mp he'
    exact (rationalCodeLT_congr hc hc'C he he'C hcc' hee').mpr h
  · intro h
    exact ⟨c, (mem_rationalClass_iff c c).mpr ⟨hc, rationalCodeEquiv_refl hc⟩,
      e, (mem_rationalClass_iff e e).mpr ⟨he, rationalCodeEquiv_refl he⟩, h⟩

theorem internalRational_exists_rep {q : V} (hq : q ∈ internalRationals V) :
    ∃ r : InternalRationalRep V, q = rationalClass r.code := by
  obtain ⟨c, hc, rfl⟩ := (mem_internalRationals_iff q).mp hq
  obtain ⟨r, rfl⟩ := rationalCode_exists_rep hc
  exact ⟨r, rfl⟩

theorem internalRationalLT_reps_iff (r s : InternalRationalRep V) :
    InternalRationalLT (rationalClass r.code) (rationalClass s.code) ↔ r.Less s :=
  (internalRationalLT_classes_iff r.code_mem s.code_mem).trans (r.lt_code_iff s)

theorem internalRationalLT_irrefl {q : V} (hq : q ∈ internalRationals V) :
    ¬ InternalRationalLT q q := by
  obtain ⟨r, rfl⟩ := internalRational_exists_rep hq
  rw [internalRationalLT_reps_iff]
  exact r.less_irrefl

theorem internalRationalLT_trans {q r s : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hs : s ∈ internalRationals V)
    (hqr : InternalRationalLT q r) (hrs : InternalRationalLT r s) : InternalRationalLT q s := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  obtain ⟨c, rfl⟩ := internalRational_exists_rep hs
  rw [internalRationalLT_reps_iff] at hqr hrs ⊢
  exact InternalRationalRep.less_trans hqr hrs

theorem internalRational_trichotomy {q r : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) : InternalRationalLT q r ∨ q = r ∨ InternalRationalLT r q := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  rw [internalRationalLT_reps_iff, internalRationalLT_reps_iff,
    rationalClass_eq_iff a.code_mem b.code_mem, InternalRationalRep.equiv_code_iff]
  exact a.trichotomy b

theorem internalRational_dense {q r : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (hqr : InternalRationalLT q r) :
    ∃ s ∈ internalRationals V, InternalRationalLT q s ∧ InternalRationalLT s r := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  obtain ⟨b, rfl⟩ := internalRational_exists_rep hr
  have h := (internalRationalLT_reps_iff a b).mp hqr
  refine ⟨rationalClass (a.midpoint b).code,
    rationalClass_mem_internalRationals (a.midpoint b).code_mem, ?_, ?_⟩
  · exact (internalRationalLT_reps_iff _ _).mpr (InternalRationalRep.less_midpoint h)
  · exact (internalRationalLT_reps_iff _ _).mpr (InternalRationalRep.midpoint_less h)

theorem internalRational_noEndpoints {q : V} (hq : q ∈ internalRationals V) :
    (∃ r ∈ internalRationals V, InternalRationalLT r q) ∧
      ∃ s ∈ internalRationals V, InternalRationalLT q s := by
  obtain ⟨a, rfl⟩ := internalRational_exists_rep hq
  constructor
  · exact ⟨rationalClass a.previous.code, rationalClass_mem_internalRationals a.previous.code_mem,
      (internalRationalLT_reps_iff _ _).mpr a.previous_less⟩
  · exact ⟨rationalClass a.next.code, rationalClass_mem_internalRationals a.next.code_mem,
      (internalRationalLT_reps_iff _ _).mpr a.less_next⟩

end ZFVP
