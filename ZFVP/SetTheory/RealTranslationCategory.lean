import ZFVP.SetTheory.RealTranslationImages
import ZFVP.SetTheory.RealCategoryClosure

/-! Translation preserves the internal rational codes for category. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realTranslateImage_nowhereDense (r : InternalRational V) {P : V}
    (hP : IsRealNowhereDense P) : IsRealNowhereDense (realTranslateImage r.val P) := by
  refine ⟨realTranslateImage_subset_reals r hP.1, ?_⟩
  intro a ha b hb hab
  let p : InternalRational V := ⟨a, ha⟩
  let q : InternalRational V := ⟨b, hb⟩
  obtain ⟨u, hu, v, hv, hpu, huv, hvq, hmiss⟩ :=
    hP.2 (p - r).val (p - r).property (q - r).val (q - r).property
      (show p - r < q - r from sub_lt_sub_right hab r)
  let s : InternalRational V := ⟨u, hu⟩
  let t : InternalRational V := ⟨v, hv⟩
  have hadd : ∀ c d : InternalRational V, c < d → c + r < d + r := by
    intro c d h
    simpa only [add_comm] using add_lt_add_right h r
  refine ⟨(s + r).val, (s + r).property, (t + r).val, (t + r).property,
    show p < s + r from (sub_lt_iff_lt_add).mp hpu,
    hadd s t huv, show t + r < q from ?_, ?_⟩
  · simpa only [sub_add_cancel] using hadd t (q - r) hvq
  · intro y hy himage
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp himage
    have hxcut := (mem_dedekindReals_iff _).mp (hP.1 x hx)
    exact hmiss x ((realTranslate_interval_iff r s t hxcut).mp hy) hx

theorem realTranslateImage_meagre (r : InternalRational V) {A : V}
    (hA : IsRealMeagre A) : IsRealMeagre (realTranslateImage r.val A) := by
  obtain ⟨f, hf, hfn, hcover⟩ := hA
  let F : V → V := fun n ↦ realClosedCode (realTranslateImage r.val (realClosedFrom (f ‘ n)))
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let g := definableGraph (ω : V) F hF
  have hcode : ∀ n ∈ (ω : V), f ‘ n ⊆ realBasicCodes V := by
    intro n hn
    exact mem_power_iff.mp (function_value_mem hf hn)
  have hspec : ∀ n ∈ (ω : V), realClosedFrom (F n) =
      realTranslateImage r.val (realClosedFrom (f ‘ n)) := by
    intro n hn
    exact realClosedCode_spec (realTranslateImage_subset_reals r (hfn n hn).1)
      (realTranslateImage_closed r (hfn n hn).1 (realClosedFrom_complement_open (hcode n hn)))
  refine ⟨g, definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n _ ↦ mem_power_iff.mpr (realClosedCode_subset _)), ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn, hspec n hn]
    exact realTranslateImage_nowhereDense r (hfn n hn)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    obtain ⟨n, hn, hxn⟩ := hcover x hx
    refine ⟨n, hn, ?_⟩
    rw [value_definableGraph _ _ _ hn, hspec n hn]
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨x, hxn, rfl⟩

theorem realTranslateImage_baireProperty (r : InternalRational V) {A : V}
    (_hA : A ⊆ dedekindReals V) (hBP : RealBaireProperty A) :
    RealBaireProperty (realTranslateImage r.val A) := by
  obtain ⟨U, hU, hM⟩ := hBP
  refine ⟨realTranslateImage r.val U, realTranslateImage_isOpen r hU,
    isRealMeagre_subset (realTranslateImage_meagre r hM) ?_⟩
  intro y hy
  rcases mem_union_iff.mp hy with hyA | hyU
  · obtain ⟨hyA, hyU⟩ := mem_sdiff_iff.mp hyA
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hyA
    have hxU : x ∉ U := fun h ↦ hyU ((mem_realTranslateImage_iff _ _ _).mpr ⟨x, h, rfl⟩)
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨x,
      mem_union_iff.mpr (Or.inl (mem_sdiff_iff.mpr ⟨hx, hxU⟩)), rfl⟩
  · obtain ⟨hyU, hyA⟩ := mem_sdiff_iff.mp hyU
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hyU
    have hxA : x ∉ A := fun h ↦ hyA ((mem_realTranslateImage_iff _ _ _).mpr ⟨x, h, rfl⟩)
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨x,
      mem_union_iff.mpr (Or.inr (mem_sdiff_iff.mpr ⟨hx, hxA⟩)), rfl⟩

theorem realTranslateImage_baireProperty_iff (r : InternalRational V) {A : V}
    (hA : A ⊆ dedekindReals V) :
    RealBaireProperty (realTranslateImage r.val A) ↔ RealBaireProperty A := by
  refine ⟨fun h ↦ ?_, realTranslateImage_baireProperty r hA⟩
  have hh := realTranslateImage_baireProperty (-r) (realTranslateImage_subset_reals r hA) h
  simpa only [realTranslateImage_inverse r hA] using hh

end ZFVP
