import ZFVP.SetTheory.RealCoverInfimum

/-! Addition of extended nonnegative cuts, including the full rational cut at infinity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def extendedRealAddFormula : SetTheorySemisentence 3 :=
  f“w u v. ∀ q, q ∈ w ↔ q ∈ !internalRationalsFormula ∧
    ∃ p ∈ u, ∃ r ∈ v, q = !rationalAddFormula p r”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def extendedRealAdd (u v : V) : V :=
  {q ∈ internalRationals V ; ∃ p ∈ u, ∃ r ∈ v, q = rationalAdd p r}

theorem mem_extendedRealAdd_iff (u v q : V) : q ∈ extendedRealAdd u v ↔
    q ∈ internalRationals V ∧ ∃ p ∈ u, ∃ r ∈ v, q = rationalAdd p r := by
  simp [extendedRealAdd]

instance extendedRealAddFormula_defined :
    ℒₛₑₜ-function₂[V] extendedRealAdd via extendedRealAddFormula :=
  ⟨fun v ↦ by simp [extendedRealAddFormula, mem_ext_iff (y := extendedRealAdd _ _),
    mem_extendedRealAdd_iff]⟩

instance extendedRealAdd_definable : ℒₛₑₜ-function₂[V] extendedRealAdd :=
  extendedRealAddFormula_defined.to_definable

theorem extendedRealAdd_comm {u v : V} (hu : u ⊆ internalRationals V) (hv : v ⊆ internalRationals V) :
    extendedRealAdd u v = extendedRealAdd v u := by
  apply mem_ext
  intro q
  simp only [mem_extendedRealAdd_iff]
  constructor
  · rintro ⟨hq, p, hp, r, hr, he⟩
    exact ⟨hq, r, hr, p, hp, he.trans (rationalAdd_comm (hu p hp) (hv r hr))⟩
  · rintro ⟨hq, p, hp, r, hr, he⟩
    exact ⟨hq, r, hr, p, hp, he.trans (rationalAdd_comm (hv p hp) (hu r hr))⟩

theorem extendedRealAdd_mono {u v s t : V} (hus : u ⊆ s) (hvt : v ⊆ t) :
    extendedRealAdd u v ⊆ extendedRealAdd s t := by
  intro q hq
  obtain ⟨hqQ, p, hp, r, hr, he⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
  exact (mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, p, hus p hp, r, hvt r hr, he⟩

theorem extendedRealAdd_extended {u v : V}
    (hu : IsExtendedNonnegativeReal u) (hv : IsExtendedNonnegativeReal v) :
    IsExtendedNonnegativeReal (extendedRealAdd u v) := by
  refine ⟨fun q hq ↦ ((mem_extendedRealAdd_iff _ _ _).mp hq).1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqQ, hq0⟩ := (mem_rationalCut_iff _ _).mp hq
    let a : InternalRational V := ⟨q, hqQ⟩
    have hhalf : a / 2 < 0 := div_neg_of_neg_of_pos hq0 zero_lt_two
    have hm : (a / 2).val ∈ rationalCut (rationalZero V) :=
      (mem_rationalCut_iff _ _).mpr ⟨(a / 2).property, hhalf⟩
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, (a / 2).val, hu.2.1 _ hm,
      (a / 2).val, hv.2.1 _ hm, ?_⟩
    exact congrArg Subtype.val (show a = a / 2 + a / 2 from (add_halves a).symm)
  · intro q hq t ht htq
    obtain ⟨_, p, hp, r, hr, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    let a : InternalRational V := ⟨t, ht⟩
    let b : InternalRational V := ⟨p, hu.1 p hp⟩
    let c : InternalRational V := ⟨r, hv.1 r hr⟩
    have hab : a - c < b := (sub_lt_iff_lt_add).mpr (show a < b + c from htq)
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨ht, (a - c).val,
      hu.2.2.1 p hp _ (a - c).property hab, r, hr, ?_⟩
    exact congrArg Subtype.val (show a = (a - c) + c from (sub_add_cancel a c).symm)
  · intro q hq
    obtain ⟨_, p, hp, r, hr, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    obtain ⟨s, hs, hps⟩ := hu.2.2.2 p hp
    refine ⟨rationalAdd s r,
      (mem_extendedRealAdd_iff _ _ _).mpr ⟨rationalAdd_mem (hu.1 s hs) (hv.1 r hr), s, hs, r, hr, rfl⟩, ?_⟩
    exact rationalAdd_lt_right (hu.1 p hp) (hu.1 s hs) (hv.1 r hr) hps

theorem extendedRealAdd_zero {u : V} (hu : IsExtendedNonnegativeReal u) :
    extendedRealAdd u (rationalCut (rationalZero V)) = u := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨hqQ, p, hp, r, hr, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    obtain ⟨hrQ, hr0⟩ := (mem_rationalCut_iff _ _).mp hr
    let a : InternalRational V := ⟨p, hu.1 p hp⟩
    let b : InternalRational V := ⟨r, hrQ⟩
    exact hu.2.2.1 p hp _ hqQ (show a + b < a from add_lt_of_neg_right a (show b < 0 from hr0))
  · intro hq
    obtain ⟨p, hp, hqp⟩ := hu.2.2.2 q hq
    let a : InternalRational V := ⟨q, hu.1 q hq⟩
    let b : InternalRational V := ⟨p, hu.1 p hp⟩
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨a.property, p, hp, (a - b).val,
      (mem_rationalCut_iff _ _).mpr ⟨(a - b).property, (show a - b < (0 : InternalRational V) from sub_neg.mpr (show a < b from hqp))⟩, ?_⟩
    exact congrArg Subtype.val (show a = b + (a - b) from by ring)

theorem extendedRealAdd_zero_left {u : V} (hu : IsExtendedNonnegativeReal u) :
    extendedRealAdd (rationalCut (rationalZero V)) u = u := by
  rw [extendedRealAdd_comm (fun _ h ↦ ((mem_rationalCut_iff _ _).mp h).1) hu.1]
  exact extendedRealAdd_zero hu

theorem extendedRealAdd_assoc {u v w : V}
    (hu : u ⊆ internalRationals V) (hv : v ⊆ internalRationals V)
    (hw : w ⊆ internalRationals V) :
    extendedRealAdd (extendedRealAdd u v) w = extendedRealAdd u (extendedRealAdd v w) := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨hqQ, p, hp, c, hc, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    obtain ⟨_, a, ha, b, hb, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hp
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, a, ha, rationalAdd b c,
      (mem_extendedRealAdd_iff _ _ _).mpr ⟨rationalAdd_mem (hv b hb) (hw c hc),
        b, hb, c, hc, rfl⟩, ?_⟩
    exact congrArg Subtype.val (add_assoc (⟨a, hu a ha⟩ : InternalRational V)
      ⟨b, hv b hb⟩ ⟨c, hw c hc⟩)
  · intro hq
    obtain ⟨hqQ, a, ha, p, hp, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    obtain ⟨_, b, hb, c, hc, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hp
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, rationalAdd a b,
      (mem_extendedRealAdd_iff _ _ _).mpr ⟨rationalAdd_mem (hu a ha) (hv b hb),
        a, ha, b, hb, rfl⟩, c, hc, ?_⟩
    exact congrArg Subtype.val (add_assoc (⟨a, hu a ha⟩ : InternalRational V)
      ⟨b, hv b hb⟩ ⟨c, hw c hc⟩).symm

theorem extendedRealAdd_le_left {u v : V}
    (hu : IsExtendedNonnegativeReal u) (hv : IsExtendedNonnegativeReal v) :
    u ⊆ extendedRealAdd u v := by
  have h := extendedRealAdd_mono (u := u) (s := u) (fun _ h ↦ h) hv.2.1
  rwa [extendedRealAdd_zero hu] at h

theorem extendedRealAdd_le_right {u v : V}
    (hu : IsExtendedNonnegativeReal u) (hv : IsExtendedNonnegativeReal v) :
    v ⊆ extendedRealAdd u v := by
  rw [extendedRealAdd_comm hu.1 hv.1]
  exact extendedRealAdd_le_left hv hu

theorem extendedRealAdd_infinity {u : V} (hu : IsExtendedNonnegativeReal u) :
    extendedRealAdd u (internalRationals V) = internalRationals V := by
  apply mem_ext
  intro q
  constructor
  · exact fun h ↦ ((mem_extendedRealAdd_iff _ _ _).mp h).1
  · intro hq
    let a : InternalRational V := ⟨q, hq⟩
    have hm : (-1 : InternalRational V).val ∈ u :=
      hu.2.1 _ ((mem_rationalCut_iff _ _).mpr ⟨(-1 : InternalRational V).property,
        (show (-1 : InternalRational V) < 0 from neg_one_lt_zero)⟩)
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨hq, (-1 : InternalRational V).val,
      hm, (a + 1).val, (a + 1).property, ?_⟩
    exact congrArg Subtype.val (show a = -1 + (a + 1) from by ring)

theorem extendedRealAdd_rationalCuts (a b : InternalRational V) :
    extendedRealAdd (rationalCut a.val) (rationalCut b.val) = rationalCut (a + b).val := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨hqQ, p, hp, r, hr, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
    obtain ⟨hpQ, hpa⟩ := (mem_rationalCut_iff _ _).mp hp
    obtain ⟨hrQ, hrb⟩ := (mem_rationalCut_iff _ _).mp hr
    exact (mem_rationalCut_iff _ _).mpr ⟨hqQ,
      (show (⟨p, hpQ⟩ : InternalRational V) + ⟨r, hrQ⟩ < a + b from
        add_lt_add (show (⟨p, hpQ⟩ : InternalRational V) < a from hpa)
          (show (⟨r, hrQ⟩ : InternalRational V) < b from hrb))⟩
  · intro hq
    obtain ⟨hqQ, hqab⟩ := (mem_rationalCut_iff _ _).mp hq
    let c : InternalRational V := ⟨q, hqQ⟩
    let e := (a + b - c) / 2
    have he : 0 < e := div_pos (sub_pos.mpr (show c < a + b from hqab)) (by norm_num)
    refine (mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, (a - e).val,
      (mem_rationalCut_iff _ _).mpr ⟨(a - e).property,
        (show a - e < a from sub_lt_self a he)⟩, (b - e).val,
      (mem_rationalCut_iff _ _).mpr ⟨(b - e).property,
        (show b - e < b from sub_lt_self b he)⟩, ?_⟩
    exact congrArg Subtype.val (show c = (a - e) + (b - e) from by dsimp [e]; ring)

end ZFVP
