import ZFVP.SetTheory.RealCountableMeasurableUnions
import ZFVP.SetTheory.RealIntervalsMeasurable
import ZFVP.SetTheory.RealGDeltaCodes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realOpenFrom_lebesgueMeasurable (hCC : InternalCountableChoice V) {S : V}
    (hS : S ⊆ realBasicCodes V) : IsRealLebesgueMeasurable (realOpenFrom S) := by
  by_cases hS0 : S = ∅
  · subst S
    have he : realOpenFrom (∅ : V) = ∅ := by
      apply mem_ext
      intro x
      simp [mem_realOpenFrom_iff]
    rw [he]
    exact realNull_lebesgueMeasurable realNull_empty
  have hSc : S ≤# (ω : V) :=
    (cardLE_of_subset (fun p hp ↦ ((mem_realBasicCodes_iff _).mp (hS p hp)).1)).trans
      ((prod_cardLE_prod internalRationals_countable internalRationals_countable).trans omega_prod_cardLE_omega)
  have hSne : IsNonempty S := ne_empty_iff_isNonempty.mp hS0
  obtain ⟨e, he, her⟩ := surjection_of_injection hSc hSne
  have : IsFunction e := IsFunction.of_mem he
  let f := definableGraph (ω : V) (fun n ↦ realInterval (kpair.π₁ (e ‘ n)) (kpair.π₂ (e ‘ n))) (by definability)
  have hf : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (f ‘ n) := by
    intro n hn
    rw [value_definableGraph _ _ _ hn]
    have hp := hS _ (function_value_mem he hn)
    obtain ⟨a, ha, b, hb, heq⟩ := mem_prod_iff.mp ((mem_realBasicCodes_iff _).mp hp).1
    rw [heq, kpair.π₁_kpair, kpair.π₂_kpair]
    exact realInterval_lebesgueMeasurable ⟨a, ha⟩ ⟨b, hb⟩
  have hU : realSequenceUnion f = realOpenFrom S := by
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨hxR, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hx
      rw [value_definableGraph _ _ _ hn] at hxn
      exact (mem_realOpenFrom_iff _ _).mpr ⟨hxR, e ‘ n, function_value_mem he hn, hxn⟩
    · intro hx
      obtain ⟨hxR, p, hp, hxp⟩ := (mem_realOpenFrom_iff _ _).mp hx
      have hpr : p ∈ range e := her.symm ▸ hp
      obtain ⟨n, hnp⟩ := mem_range_iff.mp hpr
      have hn : n ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hnp
      refine (mem_realSequenceUnion_iff _ _).mpr ⟨hxR, n, hn, ?_⟩
      rw [value_definableGraph _ _ _ hn, value_eq_of_kpair_mem hnp]
      exact hxp
  rw [← hU]
  exact realSequenceUnion_measurable hCC hf

theorem realOpen_lebesgueMeasurable (hCC : InternalCountableChoice V) {U : V}
    (hU : IsRealOpen U) : IsRealLebesgueMeasurable U := by
  obtain ⟨S, hS, rfl⟩ := hU
  exact realOpenFrom_lebesgueMeasurable hCC hS

theorem realClosed_lebesgueMeasurable (hCC : InternalCountableChoice V) {F : V}
    (hF : F ⊆ dedekindReals V) (hopen : IsRealOpen ((dedekindReals V) \ F)) :
    IsRealLebesgueMeasurable F := by
  have h := realLebesgueMeasurable_complement (realOpen_lebesgueMeasurable hCC hopen)
  have he : (dedekindReals V) \ ((dedekindReals V) \ F) = F := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff]
    have hh := hF x
    tauto
  rwa [he] at h

noncomputable def realSequenceIntersection (f : V) : V :=
  {x ∈ dedekindReals V ; ∀ n ∈ (ω : V), x ∈ f ‘ n}

theorem mem_realSequenceIntersection_iff (f x : V) : x ∈ realSequenceIntersection f ↔
    x ∈ dedekindReals V ∧ ∀ n ∈ (ω : V), x ∈ f ‘ n := by simp [realSequenceIntersection]

instance realSequenceIntersection_definable : ℒₛₑₜ-function₁[V] realSequenceIntersection := by
  have h : ℒₛₑₜ-relation[V] (fun S f ↦ ∀ x, x ∈ S ↔ x ∈ dedekindReals V ∧
    ∀ n ∈ (ω : V), x ∈ f ‘ n) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_realSequenceIntersection_iff]

theorem realSequenceIntersection_measurable (hCC : InternalCountableChoice V) {f : V}
    (hf : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (f ‘ n)) :
    IsRealLebesgueMeasurable (realSequenceIntersection f) := by
  let c := definableGraph (ω : V) (fun n ↦ (dedekindReals V) \ f ‘ n) (by definability)
  have hc : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (c ‘ n) := by
    intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact realLebesgueMeasurable_complement (hf n hn)
  have h := realLebesgueMeasurable_complement (realSequenceUnion_measurable hCC hc)
  have he : (dedekindReals V) \ realSequenceUnion c = realSequenceIntersection f := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_realSequenceUnion_iff, mem_realSequenceIntersection_iff]
    constructor
    · rintro ⟨hxR, hout⟩
      refine ⟨hxR, fun n hn ↦ ?_⟩
      by_contra hxn
      apply hout
      refine ⟨(mem_dedekindReals_iff _).mp hxR, n, hn, ?_⟩
      rw [value_definableGraph _ _ _ hn]
      exact mem_sdiff_iff.mpr ⟨hxR, hxn⟩
    · rintro ⟨hxR, hall⟩
      refine ⟨hxR, ?_⟩
      rintro ⟨_, n, hn, hxn⟩
      rw [value_definableGraph _ _ _ hn] at hxn
      exact (mem_sdiff_iff.mp hxn).2 (hall n hn)
  rwa [he] at h

theorem realGDelta_lebesgueMeasurable (hCC : InternalCountableChoice V) {g : V}
    (hg : g ∈ (℘ (realBasicCodes V)) ^ (ω : V)) : IsRealLebesgueMeasurable (realGDelta g) := by
  let f := definableGraph (ω : V) (fun n ↦ realOpenFrom (g ‘ n)) (by definability)
  have hf : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (f ‘ n) := by
    intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact realOpenFrom_lebesgueMeasurable hCC (mem_power_iff.mp (function_value_mem hg hn))
  have h := realSequenceIntersection_measurable hCC hf
  have he : realSequenceIntersection f = realGDelta g := by
    apply mem_ext
    intro x
    simp only [mem_realSequenceIntersection_iff, mem_realGDelta_iff, mem_dedekindReals_iff]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun n hn ↦ by simpa only [f, value_definableGraph _ _ _ hn] using hall n hn⟩
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun n hn ↦ by simpa only [f, value_definableGraph _ _ _ hn] using hall n hn⟩
  rwa [he] at h

end ZFVP

