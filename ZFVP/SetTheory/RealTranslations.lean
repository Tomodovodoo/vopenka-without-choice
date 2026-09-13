import ZFVP.SetTheory.DedekindRealTopology

/-! Rational translations of actual internal Dedekind cuts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realTranslateFormula : SetTheorySemisentence 3 :=
  f“y r x. ∀ q, q ∈ y ↔ q ∈ !internalRationalsFormula ∧
    !rationalAddFormula q (!rationalNegFormula r) ∈ x”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realTranslate (r x : V) : V :=
  {q ∈ internalRationals V ; rationalAdd q (rationalNeg r) ∈ x}

theorem mem_realTranslate_iff (r x q : V) : q ∈ realTranslate r x ↔
    q ∈ internalRationals V ∧ rationalAdd q (rationalNeg r) ∈ x := by
  simp [realTranslate]

instance realTranslateFormula_defined :
    ℒₛₑₜ-function₂[V] realTranslate via realTranslateFormula :=
  ⟨fun v ↦ by simp [realTranslateFormula, mem_ext_iff (y := realTranslate _ _),
    mem_realTranslate_iff]⟩

instance realTranslate_definable : ℒₛₑₜ-function₂[V] realTranslate :=
  realTranslateFormula_defined.to_definable

theorem mem_realTranslate_typed (r q : InternalRational V) (x : V) :
    q.val ∈ realTranslate r.val x ↔ (q - r).val ∈ x := by
  simp only [mem_realTranslate_iff, q.property, true_and]
  rfl

theorem realTranslate_isCut (r : InternalRational V) {x : V} (hx : IsDedekindCut x) :
    IsDedekindCut (realTranslate r.val x) := by
  refine ⟨fun q hq ↦ ((mem_realTranslate_iff _ _ _).mp hq).1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hx.2.1
    let p : InternalRational V := ⟨q, hx.1 q hq⟩
    refine ⟨(p + r).val, (mem_realTranslate_typed r (p + r) x).mpr ?_⟩
    simpa using hq
  · obtain ⟨q, hq, hqx⟩ := hx.2.2.1
    let p : InternalRational V := ⟨q, hq⟩
    refine ⟨(p + r).val, (p + r).property, ?_⟩
    intro h
    have hh := (mem_realTranslate_typed r (p + r) x).mp h
    exact hqx (by simpa using hh)
  · intro q hq p hp hpq
    let a : InternalRational V := ⟨p, hp⟩
    let b : InternalRational V := ⟨q, ((mem_realTranslate_iff _ _ _).mp hq).1⟩
    apply (mem_realTranslate_typed r a x).mpr
    have hb := (mem_realTranslate_typed r b x).mp hq
    exact hx.2.2.2.1 _ hb _ (a - r).property (show a - r < b - r from sub_lt_sub_right hpq r)
  · intro q hq
    let a : InternalRational V := ⟨q, ((mem_realTranslate_iff _ _ _).mp hq).1⟩
    have ha := (mem_realTranslate_typed r a x).mp hq
    obtain ⟨p, hp, hap⟩ := hx.2.2.2.2 _ ha
    let b : InternalRational V := ⟨p, hx.1 p hp⟩
    refine ⟨(b + r).val, (mem_realTranslate_typed r (b + r) x).mpr (by simpa using hp), ?_⟩
    exact (sub_lt_iff_lt_add).mp (show a - r < b from hap)

theorem realTranslate_zero {x : V} (hx : x ⊆ internalRationals V) :
    realTranslate (rationalZero V) x = x := by
  apply mem_ext
  intro q
  constructor
  · intro h
    obtain ⟨hq, _⟩ := (mem_realTranslate_iff _ _ _).mp h
    have hh := (mem_realTranslate_typed (0 : InternalRational V) ⟨q, hq⟩ x).mp h
    simpa using hh
  · intro h
    apply (mem_realTranslate_typed (0 : InternalRational V) ⟨q, hx q h⟩ x).mpr
    simpa using h

theorem realTranslate_comp (r s : InternalRational V) (x : V) :
    realTranslate r.val (realTranslate s.val x) = realTranslate (r + s).val x := by
  apply mem_ext
  intro q
  by_cases hq : q ∈ internalRationals V
  · let a : InternalRational V := ⟨q, hq⟩
    rw [mem_realTranslate_typed r a, mem_realTranslate_typed s (a - r),
      mem_realTranslate_typed (r + s) a]
    rw [sub_sub]
  · simp only [mem_realTranslate_iff, hq, false_and]

theorem realTranslate_inverse (r : InternalRational V) {x : V}
    (hx : x ⊆ internalRationals V) : realTranslate (-r).val (realTranslate r.val x) = x := by
  rw [realTranslate_comp, neg_add_cancel]
  exact realTranslate_zero hx

theorem realTranslate_subset (r : V) {x y : V} (hxy : x ⊆ y) :
    realTranslate r x ⊆ realTranslate r y := by
  intro q hq
  obtain ⟨hqQ, hqx⟩ := (mem_realTranslate_iff _ _ _).mp hq
  exact (mem_realTranslate_iff _ _ _).mpr ⟨hqQ, hxy _ hqx⟩

theorem realTranslate_subset_iff (r : InternalRational V) {x y : V}
    (hx : x ⊆ internalRationals V) (hy : y ⊆ internalRationals V) :
    realTranslate r.val x ⊆ realTranslate r.val y ↔ x ⊆ y := by
  refine ⟨fun h ↦ ?_, realTranslate_subset r.val⟩
  have hh := realTranslate_subset (-r).val h
  simpa only [realTranslate_inverse r hx, realTranslate_inverse r hy] using hh

theorem realTranslate_rationalCut (r q : InternalRational V) :
    realTranslate r.val (rationalCut q.val) = rationalCut (q + r).val := by
  apply mem_ext
  intro p
  by_cases hp : p ∈ internalRationals V
  · let a : InternalRational V := ⟨p, hp⟩
    rw [mem_realTranslate_typed r a, mem_rationalCut_iff, mem_rationalCut_iff]
    simp only [(a - r).property, hp, true_and]
    exact (sub_lt_iff_lt_add : a - r < q ↔ a < q + r)
  · simp only [mem_realTranslate_iff, mem_rationalCut_iff, hp, false_and]

theorem realTranslate_eq_iff (r : InternalRational V) {x y : V}
    (hx : x ⊆ internalRationals V) (hy : y ⊆ internalRationals V) :
    realTranslate r.val x = realTranslate r.val y ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (realTranslate (-r).val) h
    simpa only [realTranslate_inverse r hx, realTranslate_inverse r hy] using hh
  · exact congrArg (realTranslate r.val)

theorem realTranslate_lt_iff (r : InternalRational V) {x y : V}
    (hx : IsDedekindCut x) (hy : IsDedekindCut y) :
    DedekindLT (realTranslate r.val x) (realTranslate r.val y) ↔ DedekindLT x y := by
  simp only [dedekindLT_iff, ne_eq, realTranslate_subset_iff r hx.1 hy.1,
    realTranslate_eq_iff r hx.1 hy.1]

theorem realTranslate_interval_iff (r a b : InternalRational V) {x : V}
    (hx : IsDedekindCut x) :
    realTranslate r.val x ∈ realInterval (a + r).val (b + r).val ↔
      x ∈ realInterval a.val b.val := by
  rw [mem_realInterval_iff, mem_realInterval_iff,
    ← realTranslate_rationalCut r a, ← realTranslate_rationalCut r b]
  simp only [realTranslate_isCut r hx, hx, true_and,
    realTranslate_lt_iff r (rationalCut_isCut a.property) hx,
    realTranslate_lt_iff r hx (rationalCut_isCut b.property)]

end ZFVP
