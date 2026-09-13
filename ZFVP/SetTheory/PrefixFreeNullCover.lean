import ZFVP.SetTheory.PrefixFreeWeightsSums
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.NullSets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def minimalPrefixCover (F : V) : V :=
  {s ∈ F ; ∀ t ∈ F, t ⊆ s → s = t}

theorem mem_minimalPrefixCover_iff (F s : V) : s ∈ minimalPrefixCover F ↔
    s ∈ F ∧ ∀ t ∈ F, t ⊆ s → s = t := by simp [minimalPrefixCover]

def minimalPrefixCoverFormula : SetTheorySemisentence 2 :=
  f“E F. ∀ s, s ∈ E ↔ s ∈ F ∧ ∀ t ∈ F, t ⊆ s → s = t”
instance minimalPrefixCoverFormula_defined : ℒₛₑₜ-function₁[V] minimalPrefixCover via minimalPrefixCoverFormula :=
  ⟨fun v ↦ by simp [minimalPrefixCoverFormula, mem_ext_iff (y := minimalPrefixCover _), mem_minimalPrefixCover_iff]⟩
instance minimalPrefixCover_definable : ℒₛₑₜ-function₁[V] minimalPrefixCover := minimalPrefixCoverFormula_defined.to_definable

theorem minimalPrefixCover_subset (F : V) : minimalPrefixCover F ⊆ F :=
  fun s hs ↦ ((mem_minimalPrefixCover_iff _ _).mp hs).1

theorem minimalPrefixCover_prefixFree (F : V) : BinaryPrefixFree (minimalPrefixCover F) := by
  intro s hs t ht hst
  exact (((mem_minimalPrefixCover_iff _ _).mp ht).2 s (minimalPrefixCover_subset F s hs) hst).symm

theorem minimalPrefixCover_below {F s : V} (hF : F ⊆ binarySequences V) (hs : s ∈ F) :
    ∃ t ∈ minimalPrefixCover F, t ⊆ s := by
  have : IsFunction s := binarySequence_isFunction (hF s hs)
  obtain ⟨n, hn, _⟩ := leastOrdinal_existsUnique
    (fun n : V ↦ ∃ t ∈ F, t ⊆ s ∧ domain t = n) (by definability)
    ⟨domain s, IsOrdinal.nat (binarySequence_domain_mem (hF s hs)), s, hs, subset_refl _, rfl⟩
  obtain ⟨t, ht, hts, htd⟩ := hn.2.1
  have : IsFunction t := binarySequence_isFunction (hF t ht)
  refine ⟨t, (mem_minimalPrefixCover_iff _ _).mpr ⟨ht, ?_⟩, hts⟩
  intro u hu hut
  have : IsFunction u := binarySequence_isFunction (hF u hu)
  have hdu := hn.2.2 (domain u) (IsOrdinal.nat (binarySequence_domain_mem (hF u hu)))
    ⟨u, hu, fun p hp ↦ hts p (hut p hp), rfl⟩
  have hd : domain u = domain t := SetTheory.subset_antisymm
    (domain_subset_of_subset_function hut) (htd.symm ▸ hdu)
  have he := restrict_domain_eq_of_subset hut
  rw [hd, IsFunction.restrict_eq_self t (domain t) (subset_refl _)] at he
  exact he

theorem minimalPrefixCover_covers {F x : V} (hF : F ⊆ binarySequences V)
    (_hx : x ∈ cantorSpace V) (h : ∃ s ∈ F, s ⊆ x) :
    ∃ t ∈ minimalPrefixCover F, t ⊆ x := by
  obtain ⟨s, hs, hsx⟩ := h
  obtain ⟨t, ht, hts⟩ := minimalPrefixCover_below hF hs
  exact ⟨t, ht, fun p hp ↦ hsx p (hts p hp)⟩

/-- Every finite portion of a raw sequence's range occurs within an internal finite prefix. -/
theorem finite_subset_range_bounded {f B : V} (hf : f ∈ B ^ (ω : V))
    {E : V} (hfin : IsInternallyFinite E) (hE : E ⊆ range f) :
    ∃ k ∈ (ω : V), E ⊆ prefixInitial f k := by
  have : IsFunction f := IsFunction.of_mem hf
  have hall : ∀ E, IsInternallyFinite E → E ⊆ range f →
      ∃ k ∈ (ω : V), E ⊆ prefixInitial f k := by
    apply internallyFinite_induction
      (fun E ↦ E ⊆ range f → ∃ k ∈ (ω : V), E ⊆ prefixInitial f k) (by definability)
    · intro h
      exact ⟨0, by simp, empty_subset _⟩
    · intro E e ih h
      obtain ⟨k, hk, hEk⟩ := ih (fun s hs ↦ h s (mem_insert.mpr (Or.inr hs)))
      obtain ⟨i, hi⟩ := mem_range_iff.mp (h e (mem_insert.mpr (Or.inl rfl)))
      have hiω : i ∈ (ω : V) := by
        simpa only [domain_eq_of_mem_function hf] using mem_domain_of_kpair_mem hi
      let a : InternalNatural V := ⟨k, hk⟩
      let b : InternalNatural V := ⟨succ i, ω_succ_closed hiω⟩
      refine ⟨(max a b).val, (max a b).property, ?_⟩
      intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact (mem_prefixInitial_iff _ _ _).mpr ⟨i,
          (show succ i ⊆ (max a b).val from le_max_right a b) i (mem_succ_self i),
          (value_eq_of_kpair_mem hi).symm⟩
      · obtain ⟨j, hj, he⟩ := (mem_prefixInitial_iff _ _ _).mp (hEk s hs)
        exact (mem_prefixInitial_iff _ _ _).mpr ⟨j,
          (show k ⊆ (max a b).val from le_max_left a b) j hj, he⟩
  exact hall E hfin hE

theorem prefixInitial_eq_image {f B k : V} (hf : f ∈ B ^ (ω : V)) (hk : k ⊆ (ω : V)) :
    prefixInitial f k = f “ k := by
  have : IsFunction f := IsFunction.of_mem hf
  apply mem_ext
  intro s
  rw [mem_prefixInitial_iff, mem_image_iff']
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, kpair_value_mem (by rw [domain_eq_of_mem_function hf]; exact hk i hi)⟩
  · rintro ⟨i, hi, hif⟩
    exact ⟨i, hi, (value_eq_of_kpair_mem hif).symm⟩

theorem finite_subset_raw_smallMeasure {f m : V}
    (hf : f ∈ (binarySequences V) ^ (ω : V))
    (hsmall : ∀ k ∈ (ω : V), SmallMeasure (f “ k) m)
    {E : V} (hfin : IsInternallyFinite E) (hE : E ⊆ range f) : SmallMeasure E m := by
  obtain ⟨k, hk, hEk⟩ := finite_subset_range_bounded hf hfin hE
  rw [prefixInitial_eq_image hf (IsOrdinal.toIsTransitive.transitive k hk)] at hEk
  exact smallMeasure_mono_family (hsmall k hk) hEk

end ZFVP
