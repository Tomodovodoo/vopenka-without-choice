import ZFVP.SetTheory.RationalFiniteSumReindex
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.SchroederBernstein
import ZFVP.SetTheory.RealIntervalCovers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def flattenRowIndices (e i : V) : V := {j ∈ (ω : V) ; kpair.π₁ (e ‘ j) = i}

theorem mem_flattenRowIndices_iff (e i j : V) : j ∈ flattenRowIndices e i ↔
    j ∈ (ω : V) ∧ kpair.π₁ (e ‘ j) = i := by simp [flattenRowIndices]

instance flattenRowIndices_definable : ℒₛₑₜ-function₂[V] flattenRowIndices := by
  have h : ℒₛₑₜ-relation₃[V] (fun D e i ↦ ∀ j, j ∈ D ↔ j ∈ (ω : V) ∧ kpair.π₁ (e ‘ j) = i) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_flattenRowIndices_iff]

noncomputable def flattenRowTotals (e w k : V) : V :=
  definableGraph (ω : V) (fun i ↦ rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k) (by definability)

instance flattenRowTotals_definable : ℒₛₑₜ-function₃[V] flattenRowTotals := by
  have h : ℒₛₑₜ-relation₄[V] (fun s e w k ↦ ∀ p, p ∈ s ↔ ∃ i ∈ (ω : V),
      p = ⟨i, rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [flattenRowTotals, mem_definableGraph_iff]

theorem flattenRowTotals_value (e w k : V) {i : V} (hi : i ∈ (ω : V)) :
    (flattenRowTotals e w k) ‘ i = rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k :=
  value_definableGraph _ _ _ hi

theorem flattenRowTotals_mem {w k : V} (hw : ∀ j ∈ (ω : V), w ‘ j ∈ internalRationals V)
    (hk : k ∈ (ω : V)) (e : V) : ∀ i ∈ (ω : V), (flattenRowTotals e w k) ‘ i ∈ internalRationals V := by
  intro i hi
  rw [flattenRowTotals_value _ _ _ hi]
  exact rationalPartialSum_mem (rationalMaskedWeights_mem hw _) k hk

/-- Summing row contributions recovers a finite flattened sum once the row bound
contains every row used by that finite prefix. -/
theorem flattenRowTotals_partition {e w n M : V} (hn : n ∈ (ω : V)) (hM : M ∈ (ω : V))
    (hw : ∀ j ∈ (ω : V), w ‘ j ∈ internalRationals V)
    (hrows : ∀ j ∈ n, kpair.π₁ (e ‘ j) ∈ M) :
    rationalPartialSum (flattenRowTotals e w n) M = rationalPartialSum w n := by
  have hall : ∀ k ∈ (ω : V), k ⊆ n →
      rationalPartialSum (flattenRowTotals e w k) M = rationalPartialSum w k := by
    apply naturalNumber_induction (fun k ↦ k ⊆ n →
      rationalPartialSum (flattenRowTotals e w k) M = rationalPartialSum w k) (by definability)
    · intro hk
      rw [rationalPartialSum_zero]
      have he : ∀ i ∈ (ω : V), (flattenRowTotals e w 0) ‘ i = (rationalMaskedWeights w (∅ : V)) ‘ i := by
        intro i hi
        rw [flattenRowTotals_value _ _ _ hi, rationalPartialSum_zero, rationalMaskedWeights_value _ _ hi]
        simp [rationalMaskedTerm]
      rw [rationalPartialSum_congr he M hM, rationalMaskedWeights_empty_sum _ M hM]
    · intro k hk ih hkn
      have hkin : k ∈ n := hkn k (mem_succ_self k)
      have hksub : k ⊆ n := fun j hj ↦ hkn j (mem_succ_iff.mpr (Or.inr hj))
      let r := kpair.π₁ (e ‘ k)
      have hrM : r ∈ M := hrows k hkin
      have hrω : r ∈ (ω : V) := IsTransitive.ω.transitive M hM r hrM
      let c := definableGraph (ω : V) (fun _ ↦ w ‘ k) (by definability)
      have hc : ∀ i ∈ (ω : V), c ‘ i = w ‘ k := fun i hi ↦ value_definableGraph _ _ _ hi
      have hcmem : ∀ i ∈ (ω : V), c ‘ i ∈ internalRationals V := by
        intro i hi
        rw [hc i hi]
        exact hw k hk
      have he : ∀ i ∈ (ω : V), (flattenRowTotals e w (succ k)) ‘ i =
          rationalAdd ((flattenRowTotals e w k) ‘ i) ((rationalMaskedWeights c ({r} : V)) ‘ i) := by
        intro i hi
        rw [flattenRowTotals_value _ _ _ hi, flattenRowTotals_value _ _ _ hi,
          rationalPartialSum_succ _ hk, rationalMaskedWeights_value _ _ hk, rationalMaskedWeights_value _ _ hi]
        by_cases hir : i = r
        · subst i
          simp only [rationalMaskedTerm, mem_flattenRowIndices_iff, hk, and_self,
            mem_singleton_iff, ↓reduceIte, hc r hrω, r]
        · have hri : r ≠ i := Ne.symm hir
          simp only [rationalMaskedTerm, mem_flattenRowIndices_iff, hk, true_and,
            mem_singleton_iff, hir, hri, ↓reduceIte, r] at *
      rw [rationalPartialSum_add (flattenRowTotals_mem hw hk e)
        (rationalMaskedWeights_mem hcmem ({r} : V)) he M hM,
        rationalMaskedWeights_singleton_sum hcmem hrω M hM]
      simp only [rationalMaskedTerm, hrM, ↓reduceIte, hc r hrω]
      rw [ih hksub, rationalPartialSum_succ _ hk]
  exact hall n hn (subset_refl _)

end ZFVP
