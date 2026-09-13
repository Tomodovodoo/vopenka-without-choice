import ZFVP.SetTheory.PrefixFreeWeights
import ZFVP.SetTheory.SchroederBernstein

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def prefixInitial (f k : V) : V := repl (fun i ↦ f ‘ i) (by definability) k


theorem mem_prefixInitial_iff (f k s : V) : s ∈ prefixInitial f k ↔ ∃ i ∈ k, s = f ‘ i :=
  repl_spec (by definability)

def prefixInitialFormula : SetTheorySemisentence 3 :=
  f“E f k. ∀ s, s ∈ E ↔ ∃ i ∈ k, s = !value.dfn f i”
instance prefixInitialFormula_defined : ℒₛₑₜ-function₂[V] prefixInitial via prefixInitialFormula :=
  ⟨fun v ↦ by simp [prefixInitialFormula, mem_ext_iff (y := prefixInitial _ _), mem_prefixInitial_iff]⟩
instance prefixInitial_definable : ℒₛₑₜ-function₂[V] prefixInitial := prefixInitialFormula_defined.to_definable

theorem prefixInitial_succ (f k : V) : prefixInitial f (succ k) = prefixInitial f k ∪ ({f ‘ k} : V) := by
  apply mem_ext
  intro s
  simp only [mem_prefixInitial_iff, mem_succ_iff, mem_union_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl | hi, he⟩
    · exact Or.inr he
    · exact Or.inl ⟨i, hi, he⟩
  · rintro (⟨i, hi, he⟩ | he)
    · exact ⟨i, Or.inr hi, he⟩
    · exact ⟨k, Or.inl rfl, he⟩

noncomputable def prefixWeights (f : V) : V :=
  repl (fun i ↦ ⟨i, dyadicUnit (domain (f ‘ i))⟩ₖ) (by definability) (ω : V)
theorem mem_prefixWeights_iff (f p : V) : p ∈ prefixWeights f ↔
    ∃ i ∈ (ω : V), p = ⟨i, dyadicUnit (domain (f ‘ i))⟩ₖ := repl_spec (by definability)
def prefixWeightsFormula : SetTheorySemisentence 2 :=
  f“w f. ∀ p, p ∈ w ↔ ∃ i ∈ !isω,
    p = !kpair.dfn i (!dyadicUnitFormula (!domain.dfn (!value.dfn f i)))”
instance prefixWeightsFormula_defined : ℒₛₑₜ-function₁[V] prefixWeights via prefixWeightsFormula :=
  ⟨fun v ↦ by simp [prefixWeightsFormula, mem_ext_iff (y := prefixWeights _), mem_prefixWeights_iff]⟩
instance prefixWeights_definable : ℒₛₑₜ-function₁[V] prefixWeights := prefixWeightsFormula_defined.to_definable

theorem prefixWeights_value (f : V) {i : V} (hi : i ∈ (ω : V)) :
    (prefixWeights f) ‘ i = dyadicUnit (domain (f ‘ i)) := by
  change (definableGraph (ω : V) (fun i ↦ dyadicUnit (domain (f ‘ i))) (by definability)) ‘ i = _
  exact value_eq_of_kpair_mem ((pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hi, rfl⟩)

/-- Equality for an enumeration of a finite antichain, through every internal natural. -/
theorem prefixWeights_sum_eq_shadow {f n M : V} (hn : n ∈ (ω : V)) (hM : M ∈ (ω : V))
    (hf : ∀ i ∈ n, f ‘ i ∈ binarySequences V)
    (hd : ∀ i ∈ n, domain (f ‘ i) ⊆ M)
    (ha : ∀ i ∈ n, ∀ j ∈ n, i ≠ j → Incompatible (f ‘ i) (f ‘ j)) :
    rationalPartialSum (prefixWeights f) n = binaryShadowWeight (prefixInitial f n) M := by
  have hall : ∀ k ∈ (ω : V), k ⊆ n →
      rationalPartialSum (prefixWeights f) k = binaryShadowWeight (prefixInitial f k) M := by
    apply naturalNumber_induction (fun k ↦ k ⊆ n →
      rationalPartialSum (prefixWeights f) k = binaryShadowWeight (prefixInitial f k) M) (by definability)
    · intro hk
      have he : prefixInitial f (0 : V) = ∅ := by
        apply mem_ext
        intro x
        simp [mem_prefixInitial_iff, zero_def]
      rw [rationalPartialSum_zero, he]
      unfold binaryShadowWeight
      rw [shadow_empty, binaryFiniteCard_eq (by simp : (∅ : V) ∈ ω) (CardEQ.refl _), show (∅ : V) = 0 from rfl, rationalNatural_zero]
      exact congrArg Subtype.val (show (0 : InternalRational V) = 0 * (⟨dyadicUnit M, dyadicUnit_mem hM⟩ : InternalRational V) from (zero_mul _).symm)
    · intro k hk ih hkn
      have hkn' : k ⊆ n := fun i hi ↦ hkn i (mem_succ_iff.mpr (Or.inr hi))
      have hknmem : k ∈ n := hkn k (mem_succ_self k)
      rw [rationalPartialSum_succ _ hk, prefixWeights_value _ hk, ih hkn', prefixInitial_succ,
        binaryShadowWeight_disjoint_union hM, binaryShadowWeight_singleton (hf k hknmem) hM (hd k hknmem)]
      intro t ht ht'
      obtain ⟨htt, s, hs, hst⟩ := (mem_shadow_iff _ _ _).mp ht
      obtain ⟨_, u, hu, hut⟩ := (mem_shadow_iff _ _ _).mp ht'
      obtain ⟨i, hi, hsi⟩ := (mem_prefixInitial_iff _ _ _).mp hs
      have hui := mem_singleton_iff.mp hu
      rw [hsi] at hst
      rw [hui] at hut
      have : IsFunction t := IsFunction.of_mem htt
      have : IsFunction (f ‘ i) := binarySequence_isFunction (hf i (hkn' i hi))
      have : IsFunction (f ‘ k) := binarySequence_isFunction (hf k hknmem)
      exact not_incompatible_of_subset_subset hst hut
        (ha i (hkn' i hi) k hknmem (fun he ↦ mem_irrefl k (he ▸ hi)))
  exact hall n hn (subset_refl _)

theorem prefixWeights_sum_smallMeasure {f n M m : V} (hn : n ∈ (ω : V))
    (hM : M ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hf : ∀ i ∈ n, f ‘ i ∈ binarySequences V)
    (hd : ∀ i ∈ n, domain (f ‘ i) ⊆ M)
    (ha : ∀ i ∈ n, ∀ j ∈ n, i ≠ j → Incompatible (f ‘ i) (f ‘ j))
    (h : SmallMeasure (prefixInitial f n) m) :
    ¬InternalRationalLT (dyadicUnit m) (rationalPartialSum (prefixWeights f) n) := by
  rw [prefixWeights_sum_eq_shadow hn hM hf hd ha]
  apply binaryShadowWeight_smallMeasure_at hM hm ?_ h
  intro s hs
  obtain ⟨i, hi, rfl⟩ := (mem_prefixInitial_iff _ _ _).mp hs
  exact hd i hi

/-- Prefix freedom uses inclusion of the actual internal sequence graphs. -/
def BinaryPrefixFree (E : V) : Prop := ∀ s ∈ E, ∀ t ∈ E, s ⊆ t → s = t
instance binaryPrefixFree_definable : ℒₛₑₜ-predicate[V] BinaryPrefixFree := by
  unfold BinaryPrefixFree
  definability

theorem binaryPrefixFree_incompatible {E s t : V} (hE : E ⊆ binarySequences V)
    (hp : BinaryPrefixFree E) (hs : s ∈ E) (ht : t ∈ E) (hne : s ≠ t) : Incompatible s t := by
  classical
  have : IsFunction s := binarySequence_isFunction (hE s hs)
  have : IsFunction t := binarySequence_isFunction (hE t ht)
  have hsub : ∀ {a b : V}, IsFunction a → IsFunction b → domain a ⊆ domain b →
      ¬Incompatible a b → a ⊆ b := by
    intro a b hfa hfb hd hn p hp
    obtain ⟨X, Y, ha⟩ := hfa.mem_func
    obtain ⟨i, hi, v, hv, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ha p hp)
    have hid := mem_domain_of_kpair_mem hp
    have hval : a ‘ i = b ‘ i := by
      by_contra he
      exact hn ⟨i, hid, hd i hid, he⟩
    have hav := value_eq_of_kpair_mem hp
    rw [← hav, hval]
    exact kpair_value_mem (hd i hid)
  by_contra hinc
  let a : InternalNatural V := ⟨domain s, binarySequence_domain_mem (hE s hs)⟩
  let b : InternalNatural V := ⟨domain t, binarySequence_domain_mem (hE t ht)⟩
  rcases le_total a b with hab | hba
  · exact hne (hp s hs t ht (hsub inferInstance inferInstance hab hinc))
  · exact hne (hp t ht s hs (hsub inferInstance inferInstance hba
      (fun hi ↦ hinc (incompatible_symm hi)))).symm

theorem prefixInitial_eq_range {f n E : V} (hf : f ∈ E ^ n) : prefixInitial f n = range f := by
  have : IsFunction f := IsFunction.of_mem hf
  apply mem_ext
  intro s
  rw [mem_prefixInitial_iff, mem_range_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, kpair_value_mem (by rwa [domain_eq_of_mem_function hf])⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa only [domain_eq_of_mem_function hf] using mem_domain_of_kpair_mem hi,
      (value_eq_of_kpair_mem hi).symm⟩

/-- A finite prefix-free family has an internal enumeration whose cylinder-weight sum
is exactly its shadow cardinal divided by the common level's power of two. No choice
principle or restriction to standard natural numbers is used. -/
theorem finite_prefixFree_weight_comparison {E M m : V} (hE : E ⊆ binarySequences V)
    (hfin : IsInternallyFinite E) (hp : BinaryPrefixFree E)
    (hM : M ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hd : ∀ s ∈ E, domain s ⊆ M) (hsmall : SmallMeasure E m) :
    ∃ n ∈ (ω : V), ∃ f ∈ E ^ n, Injective f ∧ range f = E ∧
      rationalPartialSum (prefixWeights f) n =
        rationalMul (rationalNatural (binaryFiniteCard (shadow E M))) (dyadicUnit M) ∧
      ¬InternalRationalLT (dyadicUnit m) (rationalPartialSum (prefixWeights f) n) := by
  obtain ⟨n, hn, hEn⟩ := hfin
  obtain ⟨f, hf, hi, hr⟩ := exists_bijection_of_cardEQ hEn.symm
  have hv : ∀ i ∈ n, f ‘ i ∈ E := fun i hi ↦ function_value_mem hf hi
  have hb : ∀ i ∈ n, f ‘ i ∈ binarySequences V := fun i hi ↦ hE _ (hv i hi)
  have hdom : ∀ i ∈ n, domain (f ‘ i) ⊆ M := fun i hi ↦ hd _ (hv i hi)
  have ha : ∀ i ∈ n, ∀ j ∈ n, i ≠ j → Incompatible (f ‘ i) (f ‘ j) := by
    intro i hin j hjn hne
    exact binaryPrefixFree_incompatible hE hp (hv i hin) (hv j hjn)
      (fun he ↦ hne (injective_value_eq hf hi hin hjn he))
  have he : prefixInitial f n = E := (prefixInitial_eq_range hf).trans hr
  refine ⟨n, hn, f, hf, hi, hr, ?_, ?_⟩
  · simpa only [he, binaryShadowWeight] using prefixWeights_sum_eq_shadow hn hM hb hdom ha
  · apply prefixWeights_sum_smallMeasure hn hM hm hb hdom ha
    rwa [he]

end ZFVP
