import ZFVP.SetTheory.RealBorelMeasurable
import ZFVP.SetTheory.RealTranslationMeasurable
import ZFVP.SetTheory.UnitRealNullEnvelope
import ZFVP.SetTheory.RealUnitCover
import ZFVP.SetTheory.RealCategoryUnions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realLebesgueMeasurable_of_nullGDeltaEnvelope {A : V}
    (_hA : A ⊆ dedekindReals V) (henv : HasRealNullGDeltaEnvelope A)
    (hGdelta : ∀ g ∈ (℘ (realBasicCodes V)) ^ (ω : V),
      IsRealLebesgueMeasurable (realGDelta g)) : IsRealLebesgueMeasurable A := by
  obtain ⟨g, hg, hAg, hnull⟩ := henv
  have h := realLebesgueMeasurable_sdiff (hGdelta g hg) (realNull_lebesgueMeasurable hnull)
  have he : realGDelta g \ (realGDelta g \ A) = A := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff]
    have hx := hAg x
    tauto
  rwa [he] at h

theorem allUnitReal_lebesgueMeasurable_of_cantor
    (hLM : AllLebesgueMeasurable V)
    (hGdelta : ∀ g ∈ (℘ (realBasicCodes V)) ^ (ω : V),
      IsRealLebesgueMeasurable (realGDelta g)) :
    ∀ A : V, A ⊆ unitReals V → IsRealLebesgueMeasurable A := by
  intro A hA
  exact realLebesgueMeasurable_of_nullGDeltaEnvelope
    (fun x hx ↦ (mem_dedekindReals_iff _).mpr ((mem_unitReals_iff _).mp (hA x hx)).1)
    (allUnitReal_nullGDeltaEnvelope_of_cantor hLM A hA) hGdelta

theorem translated_unit_lebesgueMeasurable
    (hunitLM : ∀ A : V, A ⊆ unitReals V → IsRealLebesgueMeasurable A)
    (r : InternalRational V) {A : V}
    (hA : A ⊆ realTranslateImage r.val (unitReals V)) : IsRealLebesgueMeasurable A := by
  have hunit : unitReals V ⊆ dedekindReals V := fun x hx ↦
    (mem_dedekindReals_iff _).mpr ((mem_unitReals_iff _).mp hx).1
  have hAR : A ⊆ dedekindReals V := subset_trans hA (realTranslateImage_subset_reals r hunit)
  have hback : realTranslateImage (-r).val A ⊆ unitReals V := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    obtain ⟨z, hz, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp (hA x hx)
    rw [realTranslate_inverse r ((mem_unitReals_iff _).mp hz).1.1]
    exact hz
  have hh := (hunitLM _ hback).translate r
  have he := realTranslateImage_inverse (-r) hAR
  simp only [neg_neg] at he
  rwa [he] at hh

theorem allRealLebesgueMeasurable_of_unit_and_countableUnion
    (hunitLM : ∀ A : V, A ⊆ unitReals V → IsRealLebesgueMeasurable A)
    (hUnionMeasurable : ∀ {f : V}, (∀ n ∈ (ω : V), IsRealLebesgueMeasurable (f ‘ n)) →
      IsRealLebesgueMeasurable (realSequenceUnion f)) : AllRealLebesgueMeasurable V := by
  intro A hA
  obtain ⟨e, he, her⟩ := surjection_of_injection (internalRationals_countable (V := V))
    (show IsNonempty (internalRationals V) from ⟨rationalZero V, rationalZero_mem⟩)
  have : IsFunction e := IsFunction.of_mem he
  let F : V → V := fun n ↦ A ∩ realTranslateImage (e ‘ n) (unitReals V)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (ω : V) F hF
  have hf : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (f ‘ n) := by
    intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact translated_unit_lebesgueMeasurable hunitLM ⟨e ‘ n, function_value_mem he hn⟩
      (fun _ hx ↦ (mem_inter_iff.mp hx).2)
  have hUnion : realSequenceUnion f = A := by
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨_, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hx
      rw [value_definableGraph _ _ _ hn] at hxn
      exact (mem_inter_iff.mp hxn).1
    · intro hx
      have hxcut := (mem_dedekindReals_iff _).mp (hA x hx)
      obtain ⟨a, ha, hxa⟩ := real_mem_translated_unit hxcut
      have har : a ∈ range e := by rwa [her]
      obtain ⟨n, hna⟩ := mem_range_iff.mp har
      have hn : n ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hna
      refine (mem_realSequenceUnion_iff _ _).mpr ⟨hxcut, n, hn, ?_⟩
      rw [value_definableGraph _ _ _ hn]
      exact mem_inter_iff.mpr ⟨hx, by simpa only [value_eq_of_kpair_mem hna] using hxa⟩
  rw [← hUnion]
  exact hUnionMeasurable hf

/-- Cantor regularity implies full Caratheodory measurability on the internal real line. -/
theorem allRealLebesgueMeasurable_of_cantor (hDC : InternalDependentChoice V)
    (hLM : AllLebesgueMeasurable V) : AllRealLebesgueMeasurable V := by
  have hCC := countableChoice_of_dependentChoice hDC
  apply allRealLebesgueMeasurable_of_unit_and_countableUnion
  · exact allUnitReal_lebesgueMeasurable_of_cantor hLM
      (fun _ hg ↦ realGDelta_lebesgueMeasurable hCC hg)
  · exact fun h ↦ realSequenceUnion_measurable hCC h

end ZFVP
