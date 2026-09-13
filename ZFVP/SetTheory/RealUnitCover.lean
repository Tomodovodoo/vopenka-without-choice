import ZFVP.SetTheory.RealTranslationCategory
import ZFVP.SetTheory.UnitRealBaireTransfer

/-! The real line is covered by rational translates of the closed unit interval. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rationalNatural_succ {n : V} (hn : n ∈ (ω : V)) :
    rationalNatural (succ n) = rationalAdd (rationalNatural n) (rationalOne V) := by
  rw [← ordinalAdd_one_natural hn, rationalNatural_add hn (by simp), rationalNatural_one]

theorem real_in_rational_unit_interval {x : V} (hx : IsDedekindCut x) :
    ∃ a ∈ internalRationals V, rationalCut a ⊆ x ∧
      x ⊆ rationalCut (rationalAdd a (rationalOne V)) := by
  obtain ⟨q, hqx⟩ := hx.2.1
  have hq := hx.1 q hqx
  obtain ⟨b, hb, hbx⟩ := hx.2.2.1
  let p : InternalRational V := ⟨q, hq⟩
  let t : InternalRational V := ⟨b, hb⟩
  obtain ⟨n, hn⟩ := InternalRational.exists_natural_gt (t - p)
  have hbn : t < p + InternalRational.ofNatural n := by
    have h := (sub_lt_iff_lt_add).mp hn
    simpa only [add_comm] using h
  have hnot : rationalAdd q (rationalNatural n.val) ∉ x := by
    intro h
    exact hbx (hx.2.2.2.1 _ h b hb hbn)
  have h : ∀ k ∈ (ω : V), rationalAdd q (rationalNatural k) ∉ x →
      ∃ a ∈ internalRationals V, rationalCut a ⊆ x ∧
        x ⊆ rationalCut (rationalAdd a (rationalOne V)) := by
    apply naturalNumber_induction
      (fun k ↦ rationalAdd q (rationalNatural k) ∉ x →
        ∃ a ∈ internalRationals V, rationalCut a ⊆ x ∧
          x ⊆ rationalCut (rationalAdd a (rationalOne V))) (by definability)
    · intro h
      exact (h (by simpa only [rationalNatural_zero, rationalAdd_zero hq] using hqx)).elim
    · intro k hk ih hnext
      by_cases hkx : rationalAdd q (rationalNatural k) ∈ x
      · have ha := rationalAdd_mem hq (rationalNatural_mem hk)
        refine ⟨rationalAdd q (rationalNatural k), ha,
          ((rationalCut_lt_iff_mem hx ha).mpr hkx).1,
          dedekindCut_le_rationalCut_of_not_mem hx (rationalAdd_mem ha rationalOne_mem) ?_⟩
        rw [rationalNatural_succ hk, ← rationalAdd_assoc hq (rationalNatural_mem hk) rationalOne_mem] at hnext
        exact hnext
      · exact ih hkx
  exact h n.val n.property hnot

theorem real_mem_translated_unit {x : V} (hx : IsDedekindCut x) :
    ∃ a ∈ internalRationals V, x ∈ realTranslateImage a (unitReals V) := by
  obtain ⟨a, ha, hax, hxa⟩ := real_in_rational_unit_interval hx
  let r : InternalRational V := ⟨a, ha⟩
  have h0 : realTranslate (-r).val (rationalCut r.val) = rationalCut (rationalZero V) := by
    rw [realTranslate_rationalCut, add_neg_cancel]
    rfl
  have h1 : realTranslate (-r).val (rationalCut (r + 1).val) = rationalCut (rationalOne V) := by
    rw [realTranslate_rationalCut]
    have he : r + 1 + -r = 1 := by ring
    rw [he]
    rfl
  have hy0 := realTranslate_subset (-r).val hax
  have hy1 := realTranslate_subset (-r).val hxa
  rw [h0] at hy0
  change realTranslate (-r).val x ⊆ realTranslate (-r).val (rationalCut (r + 1).val) at hy1
  rw [h1] at hy1
  refine ⟨a, ha, (mem_realTranslateImage_iff _ _ _).mpr ⟨realTranslate (-r).val x,
    (mem_unitReals_iff _).mpr ⟨realTranslate_isCut (-r) hx, hy0, hy1⟩, ?_⟩⟩
  simpa only [neg_neg] using realTranslate_inverse (-r) hx.1

theorem translated_unit_baireProperty (h : AllBaireProperty V) (r : InternalRational V)
    {A : V} (hA : A ⊆ realTranslateImage r.val (unitReals V)) : RealBaireProperty A := by
  have hunit : unitReals V ⊆ dedekindReals V := fun x hx ↦
    (mem_dedekindReals_iff _).mpr ((mem_unitReals_iff _).mp hx).1
  have hAR : A ⊆ dedekindReals V := subset_trans hA (realTranslateImage_subset_reals r hunit)
  have hback : realTranslateImage (-r).val A ⊆ unitReals V := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    obtain ⟨z, hz, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp (hA x hx)
    rw [realTranslate_inverse r ((mem_unitReals_iff _).mp hz).1.1]
    exact hz
  have hBP := allUnitRealBaireProperty_of_cantor h _ hback
  exact (realTranslateImage_baireProperty_iff (-r) hAR).mp hBP

end ZFVP
