import ZFVP.SetTheory.RealIntervalSplitting

/-! Total covers on both sides of a rational cut, with a geometric error budget. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realLowerHalf (q : V) : V := {x ∈ dedekindReals V ; x ⊆ rationalCut q}

instance realLowerHalf_definable : ℒₛₑₜ-function₁[V] realLowerHalf := by
  have h : ℒₛₑₜ-relation (fun H q : V ↦ ∀ x, x ∈ H ↔ x ∈ dedekindReals V ∧ x ⊆ rationalCut q) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realLowerHalf]

theorem mem_realLowerHalf_iff (q x : V) : x ∈ realLowerHalf q ↔ IsDedekindCut x ∧ x ⊆ rationalCut q := by
  simp [realLowerHalf, mem_dedekindReals_iff]

noncomputable def realLeftSplitCover (d q m : V) : V :=
  definableGraph (ω : V) (fun n ↦ realSplitLeft (d ‘ n) q (dyadicUnit (succ (ordinalAdd m n)))) (by definability)

noncomputable def realRightSplitCover (d q m : V) : V :=
  definableGraph (ω : V) (fun n ↦ realSplitRight (d ‘ n) q (dyadicUnit (succ (ordinalAdd m n)))) (by definability)

theorem realLeftSplitCover_value (d q m : V) {n : V} (hn : n ∈ (ω : V)) :
    (realLeftSplitCover d q m) ‘ n = realSplitLeft (d ‘ n) q (dyadicUnit (succ (ordinalAdd m n))) :=
  value_definableGraph _ _ _ hn

theorem realRightSplitCover_value (d q m : V) {n : V} (hn : n ∈ (ω : V)) :
    (realRightSplitCover d q m) ‘ n = realSplitRight (d ‘ n) q (dyadicUnit (succ (ordinalAdd m n))) :=
  value_definableGraph _ _ _ hn

theorem realSplitCovers_mem {d m : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    (q : InternalRational V) (hm : m ∈ (ω : V)) :
    realLeftSplitCover d q.val m ∈ (realBasicCodes V) ^ (ω : V) ∧
    realRightSplitCover d q.val m ∈ (realBasicCodes V) ^ (ω : V) := by
  constructor
  · apply definableGraph_mem_function_of_mapsTo
    intro n hn
    exact (realSplit_codes (function_value_mem hd hn) q
      ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩
      (dyadicUnit_positive (ω_succ_closed (ordinalAdd_natural hm hn)))).1
  · apply definableGraph_mem_function_of_mapsTo
    intro n hn
    exact (realSplit_codes (function_value_mem hd hn) q
      ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩
      (dyadicUnit_positive (ω_succ_closed (ordinalAdd_natural hm hn)))).2

theorem realSplitCovers_cover {d T m : V} (hd : IsRealIntervalCover d T)
    (q : InternalRational V) (hm : m ∈ (ω : V)) :
    IsRealIntervalCover (realLeftSplitCover d q.val m) (T ∩ realLowerHalf q.val) ∧
    IsRealIntervalCover (realRightSplitCover d q.val m) (T \ realLowerHalf q.val) := by
  have hcodes := realSplitCovers_mem hd.1 q hm
  constructor
  · refine ⟨hcodes.1, ?_⟩
    intro x hx
    obtain ⟨hxT, hxL⟩ := mem_inter_iff.mp hx
    obtain ⟨n, hn, hxn⟩ := hd.2 x hxT
    refine ⟨n, hn, ?_⟩
    rw [realLeftSplitCover_value _ _ _ hn]
    exact realSplitLeft_covers (function_value_mem hd.1 hn) q
      ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩
      (dyadicUnit_positive (ω_succ_closed (ordinalAdd_natural hm hn))) hxn
      ((mem_realLowerHalf_iff _ _).mp hxL).2
  · refine ⟨hcodes.2, ?_⟩
    intro x hx
    obtain ⟨hxT, hxL⟩ := mem_sdiff_iff.mp hx
    obtain ⟨n, hn, hxn⟩ := hd.2 x hxT
    have hxcut := ((mem_realInterval_iff _ _ _).mp hxn).1
    have hxnot : ¬ x ⊆ rationalCut q.val := fun h ↦ hxL ((mem_realLowerHalf_iff _ _).mpr ⟨hxcut, h⟩)
    have hqx : DedekindLT (rationalCut q.val) x :=
      ⟨(dedekindCuts_comparable hxcut (rationalCut_isCut q.property)).resolve_left hxnot,
        fun h ↦ hxnot (h ▸ subset_refl _)⟩
    refine ⟨n, hn, ?_⟩
    rw [realRightSplitCover_value _ _ _ hn]
    exact realSplitRight_covers (function_value_mem hd.1 hn) q
      ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩ hxn hqx

theorem realSplitCovers_cost {d m : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    (q : InternalRational V) (hm : m ∈ (ω : V)) :
    ∀ n ∈ (ω : V), rationalAdd (realCoverCost (realLeftSplitCover d q.val m) n)
      (realCoverCost (realRightSplitCover d q.val m) n) =
      rationalAdd (realCoverCost d n) (realCoverCost (realNullPadding m) n) := by
  apply naturalNumber_induction (fun n ↦
    rationalAdd (realCoverCost (realLeftSplitCover d q.val m) n)
      (realCoverCost (realRightSplitCover d q.val m) n) =
      rationalAdd (realCoverCost d n) (realCoverCost (realNullPadding m) n)) (by definability)
  · simp only [realCoverCost_zero]
  · intro n hn ih
    rw [realCoverCost_succ _ hn, realCoverCost_succ _ hn,
      realCoverCost_succ _ hn, realCoverCost_succ _ hn]
    have hcodes := realSplitCovers_mem hd q hm
    let a : InternalRational V := ⟨_, realCoverCost_mem hcodes.1 n hn⟩
    let b : InternalRational V := ⟨_, realCoverCost_mem hcodes.2 n hn⟩
    let c : InternalRational V := ⟨_, realIntervalLength_mem (function_value_mem hcodes.1 hn)⟩
    let t : InternalRational V := ⟨_, realIntervalLength_mem (function_value_mem hcodes.2 hn)⟩
    have hswap : rationalAdd (rationalAdd a.val c.val) (rationalAdd b.val t.val) =
        rationalAdd (rationalAdd a.val b.val) (rationalAdd c.val t.val) :=
      congrArg Subtype.val (show (a + c) + (b + t) = (a + b) + (c + t) from by ring)
    change rationalAdd (rationalAdd a.val c.val) (rationalAdd b.val t.val) = _
    rw [hswap]
    change rationalAdd (rationalAdd (realCoverCost (realLeftSplitCover d q.val m) n)
      (realCoverCost (realRightSplitCover d q.val m) n))
      (rationalAdd (realIntervalLength ((realLeftSplitCover d q.val m) ‘ n))
        (realIntervalLength ((realRightSplitCover d q.val m) ‘ n))) = _
    rw [ih, realLeftSplitCover_value _ _ _ hn, realRightSplitCover_value _ _ _ hn,
      realSplit_length_sum (function_value_mem hd hn) q
        ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩,
      realNullPadding_length hm hn]
    let u : InternalRational V := ⟨_, realCoverCost_mem hd n hn⟩
    let v : InternalRational V := ⟨_, realCoverCost_mem (realNullPadding_mem hm) n hn⟩
    let w : InternalRational V := ⟨_, realIntervalLength_mem (function_value_mem hd hn)⟩
    let z : InternalRational V := ⟨_, dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))⟩
    exact congrArg Subtype.val (show (u + v) + (w + z) = (u + w) + (v + z) from by ring)

end ZFVP
