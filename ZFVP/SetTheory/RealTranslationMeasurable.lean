import ZFVP.SetTheory.RealTranslationMeasure
import ZFVP.SetTheory.RealMeasurableAlgebra

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realTranslateImage_inter (r : InternalRational V) {A B : V}
    (hA : A ⊆ dedekindReals V) (hB : B ⊆ dedekindReals V) :
    realTranslateImage r.val (A ∩ B) =
      realTranslateImage r.val A ∩ realTranslateImage r.val B := by
  apply mem_ext
  intro y
  simp only [mem_inter_iff, mem_realTranslateImage_iff]
  constructor
  · rintro ⟨x, ⟨ha, hb⟩, he⟩
    exact ⟨⟨x, ha, he⟩, ⟨x, hb, he⟩⟩
  · rintro ⟨⟨x, hx, he⟩, ⟨z, hz, hez⟩⟩
    have hxz := (realTranslate_eq_iff r
      ((mem_dedekindReals_iff _).mp (hA x hx)).1
      ((mem_dedekindReals_iff _).mp (hB z hz)).1).mp (he.trans hez.symm)
    subst z
    exact ⟨x, ⟨hx, hz⟩, he⟩

theorem realTranslateImage_sdiff (r : InternalRational V) {A B : V}
    (hA : A ⊆ dedekindReals V) (hB : B ⊆ dedekindReals V) :
    realTranslateImage r.val (A \ B) =
      realTranslateImage r.val A \ realTranslateImage r.val B := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    obtain ⟨ha, hb⟩ := mem_sdiff_iff.mp hx
    exact mem_sdiff_iff.mpr ⟨(mem_realTranslateImage_iff _ _ _).mpr ⟨x, ha, rfl⟩,
      fun h ↦ hb ((realTranslateImage_mem_iff r hB
        ((mem_dedekindReals_iff _).mp (hA x ha))).mp h)⟩
  · intro hy
    obtain ⟨ha, hb⟩ := mem_sdiff_iff.mp hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp ha
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨x,
      mem_sdiff_iff.mpr ⟨hx, fun h ↦ hb
        ((mem_realTranslateImage_iff _ _ _).mpr ⟨x, h, rfl⟩)⟩, rfl⟩

theorem IsRealLebesgueMeasurable.translate {A : V}
    (hA : IsRealLebesgueMeasurable A) (r : InternalRational V) :
    IsRealLebesgueMeasurable (realTranslateImage r.val A) := by
  refine ⟨realTranslateImage_subset_reals r hA.1, ?_⟩
  intro T hT
  let S := realTranslateImage (-r).val T
  have hS : S ⊆ dedekindReals V := realTranslateImage_subset_reals (-r) hT
  have he : realTranslateImage r.val S = T := by
    simpa only [neg_neg] using realTranslateImage_inverse (-r) hT
  have hi : realOuterMeasure (T ∩ realTranslateImage r.val A) = realOuterMeasure (S ∩ A) := by
    rw [← he, ← realTranslateImage_inter r hS hA.1]
    exact realOuterMeasure_translate r (fun _ h ↦ hS _ (mem_inter_iff.mp h).1)
  have hd : realOuterMeasure (T \ realTranslateImage r.val A) = realOuterMeasure (S \ A) := by
    rw [← he, ← realTranslateImage_sdiff r hS hA.1]
    exact realOuterMeasure_translate r (fun _ h ↦ hS _ (mem_sdiff_iff.mp h).1)
  rw [hi, hd, ← hA.2 S hS]
  exact (realOuterMeasure_translate (-r) hT).symm

end ZFVP
