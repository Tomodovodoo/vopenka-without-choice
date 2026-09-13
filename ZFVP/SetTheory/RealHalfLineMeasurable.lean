import ZFVP.SetTheory.RealCoverSumAddition

/-! Rational half-lines satisfy the full Carathéodory criterion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realLowerHalf_lebesgueMeasurable (q : InternalRational V) :
    IsRealLebesgueMeasurable (realLowerHalf q.val) := by
  apply realLebesgueMeasurable_of_split_ge
    (fun _ h ↦ (mem_dedekindReals_iff _).mpr ((mem_realLowerHalf_iff _ _).mp h).1)
  intro T _hT r hr
  by_contra hnot
  have hs := extendedRealAdd_extended (realOuterMeasure_extended (T ∩ realLowerHalf q.val))
    (realOuterMeasure_extended (T \ realLowerHalf q.val))
  obtain ⟨s, hsS, hrs⟩ := hs.2.2.2 r hr
  let a : InternalRational V := ⟨r, hs.1 r hr⟩
  let b : InternalRational V := ⟨s, hs.1 s hsS⟩
  let e := (b - a) / 4
  have he : 0 < e := div_pos (sub_pos.mpr (show a < b from hrs)) (by norm_num)
  obtain ⟨d, hd, hcost⟩ := realOuterMeasure_cover_approximation a (a + e) hnot
    (lt_add_of_pos_right a he)
  obtain ⟨m, hm, hme⟩ := dyadicUnit_small e.property he
  have hbound := realSplitCovers_outerMeasure_bound hd q (a + e) hm hcost
  have hsb : b < (a + e) + ⟨dyadicUnit m, dyadicUnit_mem hm⟩ :=
    ((mem_rationalCut_iff _ _).mp (hbound s hsS)).2
  have hδ : (⟨dyadicUnit m, dyadicUnit_mem hm⟩ : InternalRational V) < e := hme
  have heq : 4 * e = b - a := by dsimp [e]; ring
  linarith

end ZFVP
