import ZFVP.SetTheory.InterleavedSequences

/-! A cover of a union with the sum of the two cover budgets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sequenceInterleave_intervalCover {d e A B : V}
    (hd : IsRealIntervalCover d A) (he : IsRealIntervalCover e B) :
    IsRealIntervalCover (sequenceInterleave d e) (A ∪ B) := by
  refine ⟨sequenceInterleave_mem hd.1 he.1, ?_⟩
  intro x hx
  rcases mem_union_iff.mp hx with hx | hx
  · obtain ⟨n, hn, hxn⟩ := hd.2 x hx
    refine ⟨ordinalAdd n n, ordinalAdd_natural hn hn, ?_⟩
    rwa [sequenceInterleave_even hd.1 he.1 hn]
  · obtain ⟨n, hn, hxn⟩ := he.2 x hx
    refine ⟨succ (ordinalAdd n n), ω_succ_closed (ordinalAdd_natural hn hn), ?_⟩
    rwa [sequenceInterleave_odd hd.1 he.1 hn]

theorem sequenceInterleave_coverCost {d e : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) (he : e ∈ (realBasicCodes V) ^ (ω : V)) :
    ∀ n ∈ (ω : V), realCoverCost (sequenceInterleave d e) (ordinalAdd n n) =
      rationalAdd (realCoverCost d n) (realCoverCost e n) := by
  apply naturalNumber_induction (fun n ↦
    realCoverCost (sequenceInterleave d e) (ordinalAdd n n) =
      rationalAdd (realCoverCost d n) (realCoverCost e n)) (by definability)
  · rw [show (0 : V) = ∅ from rfl, ordinalAdd_zero]
    change realCoverCost (sequenceInterleave d e) 0 = rationalAdd (realCoverCost d 0) (realCoverCost e 0)
    rw [realCoverCost_zero, realCoverCost_zero, realCoverCost_zero, rationalAdd_zero rationalZero_mem]
  · intro n hn ih
    rw [natural_double_succ hn,
      realCoverCost_succ _ (ω_succ_closed (ordinalAdd_natural hn hn)),
      realCoverCost_succ _ (ordinalAdd_natural hn hn), ih,
      sequenceInterleave_even hd he hn, sequenceInterleave_odd hd he hn,
      realCoverCost_succ _ hn, realCoverCost_succ _ hn]
    let a : InternalRational V := ⟨realCoverCost d n, realCoverCost_mem hd n hn⟩
    let b : InternalRational V := ⟨realCoverCost e n, realCoverCost_mem he n hn⟩
    let c : InternalRational V := ⟨realIntervalLength (d ‘ n), realIntervalLength_mem (function_value_mem hd hn)⟩
    let t : InternalRational V := ⟨realIntervalLength (e ‘ n), realIntervalLength_mem (function_value_mem he hn)⟩
    exact congrArg Subtype.val (show (a + b + c) + t = (a + c) + (b + t) from by ring)

theorem sequenceInterleave_coverCost_bound {d e : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) (he : e ∈ (realBasicCodes V) ^ (ω : V))
    (a b : InternalRational V)
    (ha : ∀ n ∈ (ω : V), ¬ InternalRationalLT a.val (realCoverCost d n))
    (hb : ∀ n ∈ (ω : V), ¬ InternalRationalLT b.val (realCoverCost e n)) :
    ∀ n ∈ (ω : V), ¬ InternalRationalLT (a + b).val (realCoverCost (sequenceInterleave d e) n) := by
  intro n hn
  have hn2 : n ⊆ ordinalAdd n n :=
    (show (⟨n, hn⟩ : InternalNatural V) ≤ ⟨n, hn⟩ + ⟨n, hn⟩ from
      le_add_of_nonneg_right (InternalNatural.nonneg _))
  have hmono := realCoverCost_monotone (sequenceInterleave_mem hd he) hn
    (ordinalAdd_natural hn hn) hn2
  rw [sequenceInterleave_coverCost hd he n hn] at hmono
  let s : InternalRational V := ⟨realCoverCost d n, realCoverCost_mem hd n hn⟩
  let t : InternalRational V := ⟨realCoverCost e n, realCoverCost_mem he n hn⟩
  let r : InternalRational V := ⟨realCoverCost (sequenceInterleave d e) n,
    realCoverCost_mem (sequenceInterleave_mem hd he) n hn⟩
  exact (show r ≤ a + b from le_trans (show r ≤ s + t from hmono)
    (add_le_add (show s ≤ a from ha n hn) (show t ≤ b from hb n hn)))

end ZFVP
