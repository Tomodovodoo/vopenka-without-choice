import ZFVP.SetTheory.RationalFiniteSumMasks
import ZFVP.SetTheory.InfiniteDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalIndexImage (f k : V) : V := repl (fun i ↦ f ‘ i) (by definability) k

theorem mem_rationalIndexImage_iff (f k j : V) : j ∈ rationalIndexImage f k ↔ ∃ i ∈ k, j = f ‘ i :=
  repl_spec (by definability)

def rationalIndexImageFormula : SetTheorySemisentence 3 :=
  f“E f k. ∀ j, j ∈ E ↔ ∃ i ∈ k, j = !value.dfn f i”
instance rationalIndexImageFormula_defined : ℒₛₑₜ-function₂[V] rationalIndexImage via rationalIndexImageFormula :=
  ⟨fun v ↦ by simp [rationalIndexImageFormula, mem_ext_iff (y := rationalIndexImage _ _), mem_rationalIndexImage_iff]⟩
instance rationalIndexImage_definable : ℒₛₑₜ-function₂[V] rationalIndexImage := rationalIndexImageFormula_defined.to_definable

theorem rationalIndexImage_zero (f : V) : rationalIndexImage f (0 : V) = ∅ := by
  apply mem_ext
  intro j
  simp [mem_rationalIndexImage_iff, zero_def]

theorem rationalIndexImage_succ (f k : V) :
    rationalIndexImage f (succ k) = insert (f ‘ k) (rationalIndexImage f k) := by
  apply mem_ext
  intro j
  simp only [mem_rationalIndexImage_iff, mem_succ_iff, mem_insert]
  constructor
  · rintro ⟨i, rfl | hi, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨i, hi, he⟩
  · rintro (he | ⟨i, hi, he⟩)
    · exact ⟨k, Or.inl rfl, he⟩
    · exact ⟨i, Or.inr hi, he⟩

/-- Injective internal reindexing gives an exact sum over the masked image.
Only values of the reindexed sequence on the finite source domain are constrained. -/
theorem rationalFiniteSum_injective_identity {n m f w v : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hf : f ∈ m ^ n) (hi : Injective f)
    (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V)
    (hv : ∀ i ∈ n, v ‘ i = w ‘ (f ‘ i)) :
    rationalPartialSum v n = rationalPartialSum (rationalMaskedWeights w (rationalIndexImage f n)) m := by
  have hall : ∀ k ∈ (ω : V), k ⊆ n → rationalPartialSum v k =
      rationalPartialSum (rationalMaskedWeights w (rationalIndexImage f k)) m := by
    apply naturalNumber_induction
      (fun k ↦ k ⊆ n → rationalPartialSum v k =
        rationalPartialSum (rationalMaskedWeights w (rationalIndexImage f k)) m) (by definability)
    · intro hk
      rw [rationalPartialSum_zero, rationalIndexImage_zero, rationalMaskedWeights_empty_sum _ m hm]
    · intro k hk ih hkn
      have hkin : k ∈ n := hkn k (mem_succ_self k)
      have hksub : k ⊆ n := fun i hi ↦ hkn i (mem_succ_iff.mpr (Or.inr hi))
      have hjm : f ‘ k ∈ m := function_value_mem hf hkin
      have hjω : f ‘ k ∈ (ω : V) := IsTransitive.ω.transitive m hm _ hjm
      have hfresh : f ‘ k ∉ rationalIndexImage f k := by
        intro hj
        obtain ⟨i, hik, he⟩ := (mem_rationalIndexImage_iff _ _ _).mp hj
        have hki := injective_value_eq hf hi hkin (hksub i hik) he
        exact mem_irrefl k (hki.symm ▸ hik)
      rw [rationalPartialSum_succ _ hk, ih hksub, hv k hkin, rationalIndexImage_succ,
        rationalMaskedWeights_insert_sum hw hjω hfresh hm hjm]
  exact hall n hn (subset_refl _)

/-- An injective reindexing into a finite initial segment cannot increase a sum
of nonnegative internal rational weights. The indices may be nonstandard. -/
theorem rationalFiniteSum_injective_le {n m f w v : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hf : f ∈ m ^ n) (hi : Injective f)
    (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V)
    (hpos : ∀ i ∈ (ω : V), ¬InternalRationalLT (w ‘ i) (rationalZero V))
    (hv : ∀ i ∈ n, v ‘ i = w ‘ (f ‘ i)) :
    ¬InternalRationalLT (rationalPartialSum w m) (rationalPartialSum v n) := by
  rw [rationalFiniteSum_injective_identity hn hm hf hi hw hv]
  exact rationalMaskedWeights_sum_le hw hpos _ m hm

/-- The same comparison with the conventional internal function-space hypothesis. -/
theorem rationalFiniteSum_injective_le_of_function {n m f w v : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hf : f ∈ m ^ n) (hi : Injective f)
    (hw : w ∈ (internalRationals V) ^ (ω : V))
    (hpos : ∀ i ∈ (ω : V), ¬InternalRationalLT (w ‘ i) (rationalZero V))
    (hv : ∀ i ∈ n, v ‘ i = w ‘ (f ‘ i)) :
    ¬InternalRationalLT (rationalPartialSum w m) (rationalPartialSum v n) :=
  rationalFiniteSum_injective_le hn hm hf hi (fun i hi ↦ function_value_mem hw hi) hpos hv

end ZFVP
