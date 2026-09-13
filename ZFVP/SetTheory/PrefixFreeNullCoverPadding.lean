import ZFVP.SetTheory.PrefixFreeNullCoverEnumeration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def prefixPaddedTerm (g i : V) : V := by
  classical
  exact if i ∈ domain g then dyadicUnit (domain (g ‘ i)) else rationalZero V
def prefixPaddedTermFormula : SetTheorySemisentence 3 :=
  f“q g i. (i ∈ !domain.dfn g ∧ q = !dyadicUnitFormula (!domain.dfn (!value.dfn g i))) ∨
    (i ∉ !domain.dfn g ∧ q = !rationalZeroFormula)”
instance prefixPaddedTermFormula_defined : ℒₛₑₜ-function₂[V] prefixPaddedTerm via prefixPaddedTermFormula :=
  ⟨fun v ↦ by
    by_cases h : v 2 ∈ domain (v 1)
    · simp [prefixPaddedTermFormula, prefixPaddedTerm, h]
    · simp [prefixPaddedTermFormula, prefixPaddedTerm, h]⟩
instance prefixPaddedTerm_definable : ℒₛₑₜ-function₂[V] prefixPaddedTerm := prefixPaddedTermFormula_defined.to_definable

noncomputable def prefixPaddedWeights (g : V) : V :=
  repl (fun i ↦ ⟨i, prefixPaddedTerm g i⟩ₖ) (by definability) (ω : V)

theorem mem_prefixPaddedWeights_iff (g p : V) : p ∈ prefixPaddedWeights g ↔
    ∃ i ∈ (ω : V), p = ⟨i, prefixPaddedTerm g i⟩ₖ := repl_spec (by definability)

instance prefixPaddedWeights_definable : ℒₛₑₜ-function₁[V] prefixPaddedWeights := by
  have h : ℒₛₑₜ-relation[V] (fun w g ↦ ∀ p, p ∈ w ↔
      ∃ i ∈ (ω : V), p = ⟨i, prefixPaddedTerm g i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_prefixPaddedWeights_iff]
  rfl

theorem prefixPaddedWeights_value (g : V) {i : V} (hi : i ∈ (ω : V)) :
    (prefixPaddedWeights g) ‘ i = prefixPaddedTerm g i := by
  change (definableGraph (ω : V) (prefixPaddedTerm g) (by definability)) ‘ i = _
  exact value_eq_of_kpair_mem ((pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hi, rfl⟩)

theorem prefixPaddedWeights_value_inside {g i : V} (hi : i ∈ (ω : V)) (hd : i ∈ domain g) :
    (prefixPaddedWeights g) ‘ i = dyadicUnit (domain (g ‘ i)) := by
  rw [prefixPaddedWeights_value _ hi]
  simp [prefixPaddedTerm, hd]

theorem prefixPaddedWeights_value_outside {g i : V} (hi : i ∈ (ω : V)) (hd : i ∉ domain g) :
    (prefixPaddedWeights g) ‘ i = rationalZero V := by
  rw [prefixPaddedWeights_value _ hi]
  simp [prefixPaddedTerm, hd]

theorem prefixCover_sum_congr_initial {f g n : V} (hn : n ∈ (ω : V))
    (he : ∀ i ∈ n, f ‘ i = g ‘ i) : rationalPartialSum f n = rationalPartialSum g n := by
  have hall : ∀ n ∈ (ω : V), (∀ i ∈ n, f ‘ i = g ‘ i) →
      rationalPartialSum f n = rationalPartialSum g n := by
    apply naturalNumber_induction (fun n ↦ (∀ i ∈ n, f ‘ i = g ‘ i) →
      rationalPartialSum f n = rationalPartialSum g n) (by definability)
    · intro h
      simp only [rationalPartialSum_zero]
    · intro n hn ih h
      rw [rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn,
        ih (fun i hi ↦ h i (mem_succ_iff.mpr (Or.inr hi))), h n (mem_succ_self n)]
  exact hall n hn he

theorem prefixPaddedWeights_sum_inside {g k : V} (hk : k ∈ (ω : V)) (hd : k ⊆ domain g) :
    rationalPartialSum (prefixPaddedWeights g) k = rationalPartialSum (prefixWeights g) k := by
  apply prefixCover_sum_congr_initial hk
  intro i hi
  have hiω' : i ∈ (ω : V) := (IsOrdinal.toIsTransitive.transitive k hk) i hi
  rw [prefixPaddedWeights_value_inside hiω' (hd i hi), prefixWeights_value _ hiω']

theorem prefixPaddedWeights_mem {g n E : V} (hg : g ∈ E ^ n) (hE : E ⊆ binarySequences V) :
    ∀ i ∈ (ω : V), (prefixPaddedWeights g) ‘ i ∈ internalRationals V := by
  intro i hi
  by_cases hd : i ∈ domain g
  · rw [prefixPaddedWeights_value_inside hi hd]
    exact dyadicUnit_mem (binarySequence_domain_mem (hE _ (function_value_mem hg
      (by simpa only [domain_eq_of_mem_function hg] using hd))))
  · rw [prefixPaddedWeights_value_outside hi hd]
    exact rationalZero_mem

/-- Zero padding preserves every finite sum bound when the finite enumeration ends. -/
theorem prefixPaddedWeights_all_sums {g n E m : V} (hg : g ∈ E ^ n)
    (hn : n ∈ (ω : V) ∨ n = (ω : V)) (hE : E ⊆ binarySequences V) (hm : m ∈ (ω : V))
    (hbound : ∀ k ∈ (ω : V), k ⊆ n →
      ¬InternalRationalLT (dyadicUnit m) (rationalPartialSum (prefixWeights g) k)) :
    ∀ k ∈ (ω : V), ¬InternalRationalLT (dyadicUnit m)
      (rationalPartialSum (prefixPaddedWeights g) k) := by
  have hnord : IsOrdinal n := by
    rcases hn with hn | rfl
    · exact IsOrdinal.nat hn
    · infer_instance
  have hmem := prefixPaddedWeights_mem hg hE
  apply naturalNumber_induction (fun k ↦ ¬InternalRationalLT (dyadicUnit m)
      (rationalPartialSum (prefixPaddedWeights g) k)) (by definability)
  · rw [rationalPartialSum_zero]
    exact le_of_lt (InternalRational.dyadic_pos (⟨m, hm⟩ : InternalNatural V))
  · intro k hk ih
    by_cases hkn : k ∈ n
    · have hsub : succ k ⊆ n := by
        intro i hi
        rcases mem_succ_iff.mp hi with rfl | hi
        · exact hkn
        · exact hnord.toIsTransitive.transitive k hkn i hi
      rw [prefixPaddedWeights_sum_inside (ω_succ_closed hk)
        (by rwa [domain_eq_of_mem_function hg])]
      exact hbound _ (ω_succ_closed hk) hsub
    · rw [rationalPartialSum_succ _ hk, prefixPaddedWeights_value_outside hk
        (by simpa only [domain_eq_of_mem_function hg] using hkn),
        rationalAdd_zero (rationalPartialSum_mem hmem k hk)]
      exact ih

/-- The finite or countable injective prefix cover, with zero-padded weight bounds
for every internal finite partial sum, including all indices after a finite cover ends. -/
theorem isNull_prefixFree_padded_cover {A m : V} (hA : A ⊆ cantorSpace V)
    (hnull : IsNull A) (hm : m ∈ (ω : V)) :
    ∃ E, E ⊆ binarySequences V ∧ BinaryPrefixFree E ∧
      ∃ n, (n ∈ (ω : V) ∨ n = (ω : V)) ∧
        ∃ g ∈ E ^ n, Injective g ∧ range g = E ∧
          (∀ x ∈ A, ∃ i ∈ n, (g ‘ i) ⊆ x) ∧
          ∀ k ∈ (ω : V), ¬InternalRationalLT (dyadicUnit m)
            (rationalPartialSum (prefixPaddedWeights g) k) := by
  obtain ⟨E, hE, hp, n, hn, g, hg, hi, hr, hc, hb⟩ :=
    isNull_prefixFree_enumerated_cover hA hnull hm
  exact ⟨E, hE, hp, n, hn, g, hg, hi, hr, hc, prefixPaddedWeights_all_sums hg hn hE hm hb⟩

/-- Empty covers have identically zero padded sums, without a dummy cylinder. -/
theorem prefixPaddedWeights_empty_sum : ∀ k ∈ (ω : V),
    rationalPartialSum (prefixPaddedWeights (∅ : V)) k = rationalZero V := by
  apply naturalNumber_induction (fun k ↦
    rationalPartialSum (prefixPaddedWeights (∅ : V)) k = rationalZero V) (by definability)
  · exact rationalPartialSum_zero _
  · intro k hk ih
    rw [rationalPartialSum_succ _ hk, prefixPaddedWeights_value_outside hk
      (by simp), ih, rationalAdd_zero rationalZero_mem]

end ZFVP
