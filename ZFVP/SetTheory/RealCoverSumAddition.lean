import ZFVP.SetTheory.RealSplitCovers

/-! Comparing sums of cover costs using common internal finite truncations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realCoverSum_add_le_of_partial_bound {d e : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) (he : e ∈ (realBasicCodes V) ^ (ω : V))
    (b : InternalRational V)
    (hb : ∀ n ∈ (ω : V), ¬ InternalRationalLT b.val
      (rationalAdd (realCoverCost d n) (realCoverCost e n))) :
    extendedRealAdd (realCoverSum d) (realCoverSum e) ⊆ rationalCut b.val := by
  intro q hq
  obtain ⟨hqQ, p, hp, r, hr, rfl⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
  obtain ⟨hpQ, n, hn, hpn⟩ := (mem_realCoverSum_iff _ _).mp hp
  obtain ⟨hrQ, m, hm, hrm⟩ := (mem_realCoverSum_iff _ _).mp hr
  let N := ordinalAdd n m
  have hN : N ∈ (ω : V) := ordinalAdd_natural hn hm
  have hnN : n ⊆ N :=
    (show (⟨n, hn⟩ : InternalNatural V) ≤ ⟨n, hn⟩ + ⟨m, hm⟩ from
      le_add_of_nonneg_right (InternalNatural.nonneg _))
  have hmN : m ⊆ N :=
    (show (⟨m, hm⟩ : InternalNatural V) ≤ ⟨n, hn⟩ + ⟨m, hm⟩ from
      le_add_of_nonneg_left (InternalNatural.nonneg _))
  let s : InternalRational V := ⟨realCoverCost d N, realCoverCost_mem hd N hN⟩
  let t : InternalRational V := ⟨realCoverCost e N, realCoverCost_mem he N hN⟩
  have hps : (⟨p, hpQ⟩ : InternalRational V) < s :=
    lt_of_lt_of_le (show (⟨p, hpQ⟩ : InternalRational V) <
      ⟨realCoverCost d n, realCoverCost_mem hd n hn⟩ from hpn)
      (realCoverCost_monotone hd hn hN hnN)
  have hrt : (⟨r, hrQ⟩ : InternalRational V) < t :=
    lt_of_lt_of_le (show (⟨r, hrQ⟩ : InternalRational V) <
      ⟨realCoverCost e m, realCoverCost_mem he m hm⟩ from hrm)
      (realCoverCost_monotone he hm hN hmN)
  exact (mem_rationalCut_iff _ _).mpr ⟨hqQ,
    lt_of_lt_of_le (add_lt_add hps hrt) (show s + t ≤ b from hb N hN)⟩

theorem realSplitCovers_outerMeasure_bound {d T m : V} (hd : IsRealIntervalCover d T)
    (q a : InternalRational V) (hm : m ∈ (ω : V))
    (ha : ∀ n ∈ (ω : V), ¬ InternalRationalLT a.val (realCoverCost d n)) :
    extendedRealAdd (realOuterMeasure (T ∩ realLowerHalf q.val))
      (realOuterMeasure (T \ realLowerHalf q.val)) ⊆ rationalCut (a + ⟨dyadicUnit m, dyadicUnit_mem hm⟩).val := by
  have hc := realSplitCovers_cover hd q hm
  apply subset_trans (extendedRealAdd_mono (realOuterMeasure_le_coverSum hc.1)
    (realOuterMeasure_le_coverSum hc.2))
  apply realCoverSum_add_le_of_partial_bound hc.1.1 hc.2.1
  intro n hn
  rw [realSplitCovers_cost hd.1 q hm n hn]
  exact (show (⟨realCoverCost d n, realCoverCost_mem hd.1 n hn⟩ : InternalRational V) +
      ⟨realCoverCost (realNullPadding m) n, realCoverCost_mem (realNullPadding_mem hm) n hn⟩ ≤
      a + ⟨dyadicUnit m, dyadicUnit_mem hm⟩ from
    add_le_add (ha n hn) (realNullPadding_cost_bound hm hn))

end ZFVP
