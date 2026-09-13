import ZFVP.SetTheory.RealTranslationImages
import ZFVP.SetTheory.RealCoverInfimum

/-! Rational translation preserves genuine interval-cover costs and outer measure. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realIntervalTranslate (r p : V) : V :=
  ⟨rationalAdd (kpair.π₁ p) r, rationalAdd (kpair.π₂ p) r⟩ₖ

instance realIntervalTranslate_definable : ℒₛₑₜ-function₂[V] realIntervalTranslate := by
  unfold realIntervalTranslate; definability

theorem realIntervalTranslate_mem (r : InternalRational V) {p : V} (hp : p ∈ realBasicCodes V) :
    realIntervalTranslate r.val p ∈ realBasicCodes V := by
  obtain ⟨hpp, hab⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  have hab' : (⟨a, ha⟩ : InternalRational V) < ⟨b, hb⟩ := by simpa using hab
  apply (mem_realBasicCodes_iff _).mpr
  simp only [realIntervalTranslate, kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨kpair_mem_iff.mpr ⟨rationalAdd_mem ha r.property, rationalAdd_mem hb r.property⟩, ?_⟩
  exact (show (⟨a, ha⟩ : InternalRational V) + r < ⟨b, hb⟩ + r from add_lt_add_left hab' r)

theorem realIntervalTranslate_length (r : InternalRational V) {p : V} (hp : p ∈ realBasicCodes V) :
    realIntervalLength (realIntervalTranslate r.val p) = realIntervalLength p := by
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simp only [realIntervalLength, realIntervalTranslate, kpair.π₁_kpair, kpair.π₂_kpair]
  change (((⟨b, hb⟩ : InternalRational V) + r) - (⟨a, ha⟩ + r)).val =
    ((⟨b, hb⟩ : InternalRational V) - ⟨a, ha⟩).val
  congr 1
  simp only [sub_eq_add_neg, neg_add, add_assoc]
  rw [add_left_comm r (- (⟨a, ha⟩ : InternalRational V)), add_neg_cancel, add_zero]

noncomputable def realCoverTranslate (r d : V) : V :=
  definableGraph (ω : V) (fun i ↦ realIntervalTranslate r (d ‘ i)) (by definability)

instance realCoverTranslate_definable : ℒₛₑₜ-function₂[V] realCoverTranslate := by
  have h : ℒₛₑₜ-relation₃[V] (fun c r d ↦ ∀ p, p ∈ c ↔ ∃ i ∈ (ω : V), p = ⟨i, realIntervalTranslate r (d ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [realCoverTranslate, mem_definableGraph_iff]
  rfl

theorem realCoverTranslate_value (r d : V) {i : V} (hi : i ∈ (ω : V)) :
    (realCoverTranslate r d) ‘ i = realIntervalTranslate r (d ‘ i) := value_definableGraph _ _ _ hi

theorem realCoverTranslate_mem (r : InternalRational V) {d : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) : realCoverTranslate r.val d ∈ (realBasicCodes V) ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  exact fun i hi ↦ realIntervalTranslate_mem r (function_value_mem hd hi)

theorem realCoverTranslate_cost (r : InternalRational V) {d : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) :
    ∀ n ∈ (ω : V), realCoverCost (realCoverTranslate r.val d) n = realCoverCost d n := by
  apply naturalNumber_induction (fun n ↦ realCoverCost (realCoverTranslate r.val d) n = realCoverCost d n) (by definability)
  · simp only [realCoverCost_zero]
  · intro n hn ih
    rw [realCoverCost_succ _ hn, realCoverCost_succ _ hn, ih,
      realCoverTranslate_value _ _ hn, realIntervalTranslate_length r (function_value_mem hd hn)]

theorem realCoverTranslate_sum (r : InternalRational V) {d : V}
    (hd : d ∈ (realBasicCodes V) ^ (ω : V)) : realCoverSum (realCoverTranslate r.val d) = realCoverSum d := by
  apply mem_ext
  intro q
  simp only [mem_realCoverSum_iff]
  constructor <;> rintro ⟨hq, n, hn, h⟩
  · exact ⟨hq, n, hn, by rwa [realCoverTranslate_cost r hd n hn] at h⟩
  · exact ⟨hq, n, hn, by rwa [realCoverTranslate_cost r hd n hn]⟩

theorem IsRealIntervalCover.translate {d A : V} (hd : IsRealIntervalCover d A) (r : InternalRational V) :
    IsRealIntervalCover (realCoverTranslate r.val d) (realTranslateImage r.val A) := by
  refine ⟨realCoverTranslate_mem r hd.1, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
  obtain ⟨i, hi, hxi⟩ := hd.2 x hx
  obtain ⟨a, ha, b, hb, he⟩ := mem_prod_iff.mp ((mem_realBasicCodes_iff _).mp (function_value_mem hd.1 hi)).1
  rw [he, kpair.π₁_kpair, kpair.π₂_kpair] at hxi
  refine ⟨i, hi, ?_⟩
  rw [realCoverTranslate_value _ _ hi, he]
  simp only [realIntervalTranslate, kpair.π₁_kpair, kpair.π₂_kpair]
  exact (realTranslate_interval_iff r ⟨a, ha⟩ ⟨b, hb⟩ ((mem_realInterval_iff _ _ _).mp hxi).1).mpr hxi

theorem realOuterMeasure_translate_le (r : InternalRational V) (A : V) :
    realOuterMeasure (realTranslateImage r.val A) ⊆ realOuterMeasure A := by
  apply realOuterMeasure_greatest_lower_bound (realOuterMeasure_extended _)
  intro d hd
  have hh := realOuterMeasure_le_coverSum (hd.translate r)
  rwa [realCoverTranslate_sum r hd.1] at hh

theorem realOuterMeasure_translate (r : InternalRational V) {A : V} (hA : A ⊆ dedekindReals V) :
    realOuterMeasure (realTranslateImage r.val A) = realOuterMeasure A := by
  apply subset_antisymm (realOuterMeasure_translate_le r A)
  have hh := realOuterMeasure_translate_le (-r) (realTranslateImage r.val A)
  rwa [realTranslateImage_inverse r hA] at hh

theorem IsRealNull.translate {A : V} (hA : IsRealNull A) (r : InternalRational V) :
    IsRealNull (realTranslateImage r.val A) := by
  intro m hm
  obtain ⟨d, hd, hb⟩ := hA m hm
  exact ⟨realCoverTranslate r.val d, hd.translate r, fun n hn ↦ by rw [realCoverTranslate_cost r hd.1 n hn]; exact hb n hn⟩

end ZFVP
