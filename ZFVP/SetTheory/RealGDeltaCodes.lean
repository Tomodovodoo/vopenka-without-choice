import ZFVP.SetTheory.RealCoverExistence

/-! Actual real G-delta codes and null-excess envelopes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realGDeltaFormula : SetTheorySemisentence 2 :=
  f“H g. ∀ x, x ∈ H ↔ !isDedekindCutFormula x ∧
    ∀ n ∈ !isω, x ∈ !realOpenFromFormula (!value.dfn g n)”

def hasRealNullGDeltaEnvelopeFormula : SetTheorySemisentence 1 :=
  f“A. ∃ g ∈ !function.dfn (!power.dfn (!realBasicCodesFormula)) (!isω),
    A ⊆ !realGDeltaFormula g ∧ !isRealNullFormula (!sdiff.dfn (!realGDeltaFormula g) A)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realGDelta (g : V) : V :=
  {x ∈ dedekindReals V ; ∀ n ∈ (ω : V), x ∈ realOpenFrom (g ‘ n)}

theorem mem_realGDelta_iff (g x : V) : x ∈ realGDelta g ↔
    IsDedekindCut x ∧ ∀ n ∈ (ω : V), x ∈ realOpenFrom (g ‘ n) := by
  simp [realGDelta, mem_dedekindReals_iff]

instance realGDeltaFormula_defined : ℒₛₑₜ-function₁[V] realGDelta via realGDeltaFormula :=
  ⟨fun v ↦ by simp [realGDeltaFormula, mem_ext_iff (y := realGDelta _), mem_realGDelta_iff]⟩

instance realGDelta_definable : ℒₛₑₜ-function₁[V] realGDelta := realGDeltaFormula_defined.to_definable

def HasRealNullGDeltaEnvelope (A : V) : Prop :=
  ∃ g ∈ (℘ (realBasicCodes V)) ^ (ω : V), A ⊆ realGDelta g ∧ IsRealNull (realGDelta g \ A)

instance hasRealNullGDeltaEnvelopeFormula_defined :
    ℒₛₑₜ-predicate[V] HasRealNullGDeltaEnvelope via hasRealNullGDeltaEnvelopeFormula :=
  ⟨fun v ↦ by simp [hasRealNullGDeltaEnvelopeFormula, HasRealNullGDeltaEnvelope]⟩

instance hasRealNullGDeltaEnvelope_definable : ℒₛₑₜ-predicate[V] HasRealNullGDeltaEnvelope :=
  hasRealNullGDeltaEnvelopeFormula_defined.to_definable

noncomputable def realUnitThickening (n : V) : V :=
  realInterval (rationalNeg (dyadicUnit n)) (rationalAdd (rationalOne V) (dyadicUnit n))

instance realUnitThickening_definable : ℒₛₑₜ-function₁[V] realUnitThickening := by
  unfold realUnitThickening
  definability

theorem realUnitThickening_isOpen {n : V} (hn : n ∈ (ω : V)) : IsRealOpen (realUnitThickening n) :=
  realInterval_isOpen (rationalNeg_mem (dyadicUnit_mem hn)) (rationalAdd_mem rationalOne_mem (dyadicUnit_mem hn))

theorem unit_subset_realUnitThickening {n : V} (hn : n ∈ (ω : V)) :
    unitReals V ⊆ realUnitThickening n := by
  intro x hx
  obtain ⟨hxcut, h0x, hx1⟩ := (mem_unitReals_iff _).mp hx
  let d : InternalRational V := ⟨dyadicUnit n, dyadicUnit_mem hn⟩
  have hd : 0 < d := dyadicUnit_positive hn
  refine (mem_realInterval_iff _ _ _).mpr ⟨hxcut, ?_, ?_⟩
  · exact dedekindLT_of_lt_of_subset
      ((rationalCut_lt_iff (-d).property rationalZero_mem).mpr (neg_lt_zero.mpr hd)) h0x
  · exact dedekindLT_of_subset_of_lt hx1
      ((rationalCut_lt_iff rationalOne_mem (1 + d).property).mpr (lt_add_of_pos_right 1 hd))

theorem unitReals_iff_thickenings (x : V) :
    x ∈ unitReals V ↔ IsDedekindCut x ∧ ∀ n ∈ (ω : V), x ∈ realUnitThickening n := by
  constructor
  · intro hx
    exact ⟨((mem_unitReals_iff _).mp hx).1, fun _ hn ↦ unit_subset_realUnitThickening hn x hx⟩
  · rintro ⟨hxcut, hx⟩
    refine (mem_unitReals_iff _).mpr ⟨hxcut, ?_, ?_⟩
    · intro q hq
      obtain ⟨hqQ, hq0⟩ := (mem_rationalCut_iff _ _).mp hq
      let a : InternalRational V := ⟨q, hqQ⟩
      have ha : a < 0 := hq0
      obtain ⟨n, hn⟩ := InternalRational.exists_dyadic_lt (neg_pos.mpr ha)
      have hqdn : a < -InternalRational.dyadic n := by
        simpa only [neg_neg] using neg_lt_neg hn
      have hlow := ((mem_realInterval_iff _ _ _).mp (hx n.val n.property)).2.1.1
      exact hlow q ((mem_rationalCut_iff _ _).mpr ⟨hqQ, hqdn⟩)
    · intro q hqx
      obtain ⟨r, hrx, hqr⟩ := hxcut.2.2.2.2 q hqx
      let a : InternalRational V := ⟨q, hxcut.1 q hqx⟩
      let b : InternalRational V := ⟨r, hxcut.1 r hrx⟩
      obtain ⟨n, hn⟩ := InternalRational.exists_dyadic_lt (sub_pos.mpr (show a < b from hqr))
      have hupper := ((mem_realInterval_iff _ _ _).mp (hx n.val n.property)).2.2.1
      have hb : b < 1 + InternalRational.dyadic n := ((mem_rationalCut_iff _ _).mp (hupper r hrx)).2
      have ha : a + InternalRational.dyadic n < b := by
        simpa only [add_comm] using (lt_sub_iff_add_lt).mp hn
      have ha1 : a < 1 := lt_of_add_lt_add_right (lt_trans ha hb)
      exact (mem_rationalCut_iff _ _).mpr ⟨a.property, ha1⟩

end ZFVP
