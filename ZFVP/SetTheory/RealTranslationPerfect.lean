import ZFVP.SetTheory.RealUnitCover
import ZFVP.SetTheory.UnitRealPerfectTransfer

/-! Rational translations preserve perfect real sets and the exact PSP dichotomy. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem perfectRealSet_subset_reals {P : V} (hP : IsPerfectRealSet P) : P ⊆ dedekindReals V := by
  obtain ⟨S, _, he⟩ := hP.1
  intro x hx
  rw [he] at hx
  exact (mem_dedekindReals_iff _).mpr ((mem_realClosedFrom_iff _ _).mp hx).1

theorem realTranslateImage_perfect (r : InternalRational V) {P : V}
    (hP : IsPerfectRealSet P) : IsPerfectRealSet (realTranslateImage r.val P) := by
  have hPR := perfectRealSet_subset_reals hP
  have hPo : IsRealOpen ((dedekindReals V) \ P) := by
    obtain ⟨S, hS, he⟩ := hP.1
    rw [he]
    exact realClosedFrom_complement_open hS
  have hQo := realTranslateImage_closed r hPR hPo
  refine ⟨⟨realClosedCode (realTranslateImage r.val P), realClosedCode_subset _,
    (realClosedCode_spec (realTranslateImage_subset_reals r hPR) hQo).symm⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hP.2.1
    exact ⟨realTranslate r.val x, (mem_realTranslateImage_iff _ _ _).mpr ⟨x, hx, rfl⟩⟩
  · intro y hy a ha b hb hyi
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    have hxcut := (mem_dedekindReals_iff _).mp (hPR x hx)
    let p : InternalRational V := ⟨a, ha⟩
    let q : InternalRational V := ⟨b, hb⟩
    have hxi : x ∈ realInterval (p - r).val (q - r).val := by
      apply (realTranslate_interval_iff r (p - r) (q - r) hxcut).mp
      simpa only [sub_add_cancel] using hyi
    obtain ⟨z, hz, hzi, hzx⟩ := hP.2.2 x hx (p - r).val (p - r).property
      (q - r).val (q - r).property hxi
    have hzcut := (mem_dedekindReals_iff _).mp (hPR z hz)
    refine ⟨realTranslate r.val z, (mem_realTranslateImage_iff _ _ _).mpr ⟨z, hz, rfl⟩, ?_, ?_⟩
    · have hh := (realTranslate_interval_iff r (p - r) (q - r) hzcut).mpr hzi
      simpa only [sub_add_cancel] using hh
    · exact fun he ↦ hzx ((realTranslate_eq_iff r hzcut.1 hxcut.1).mp he)

theorem realTranslateImage_perfectSetProperty (r : InternalRational V) {A : V}
    (h : RealPerfectSetProperty A) : RealPerfectSetProperty (realTranslateImage r.val A) := by
  rcases h with hcount | ⟨P, hP, hPA⟩
  · exact Or.inl (internallyCountable_repl (realTranslate r.val) (by definability) hcount)
  · refine Or.inr ⟨realTranslateImage r.val P, realTranslateImage_perfect r hP, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hx
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨y, hPA y hy, rfl⟩

theorem translated_unit_perfectSetProperty (h : AllPerfectSetProperty V) (r : InternalRational V)
    {A : V} (hA : A ⊆ realTranslateImage r.val (unitReals V)) : RealPerfectSetProperty A := by
  have hunit : unitReals V ⊆ dedekindReals V := fun x hx ↦
    (mem_dedekindReals_iff _).mpr ((mem_unitReals_iff _).mp hx).1
  have hAR : A ⊆ dedekindReals V := subset_trans hA (realTranslateImage_subset_reals r hunit)
  have hback : realTranslateImage (-r).val A ⊆ unitReals V := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    obtain ⟨z, hz, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp (hA x hx)
    rw [realTranslate_inverse r ((mem_unitReals_iff _).mp hz).1.1]
    exact hz
  have hh := realTranslateImage_perfectSetProperty r
    (allUnitRealPerfectSetProperty_of_cantor h _ hback)
  have he : realTranslateImage r.val (realTranslateImage (-r).val A) = A := by
    simpa only [neg_neg] using realTranslateImage_inverse (-r) hAR
  rwa [he] at hh

end ZFVP
