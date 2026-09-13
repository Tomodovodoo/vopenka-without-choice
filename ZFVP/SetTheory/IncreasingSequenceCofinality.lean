import ZFVP.SetTheory.MonotoneCofinality
import ZFVP.SetTheory.LeastOrdinalChoice

/-! A strictly increasing sequence cofinal in a limit ordinal has the
same internal cofinality as its ordinal domain. The inverse comparison
uses the least index exceeding a value, so it needs no internal Choice. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem increasingSequence_cofinality {α δ f : V} [IsOrdinal α] [IsOrdinal δ]
    (hf : f ∈ δ ^ α)
    (hinc : ∀ i ∈ α, ∀ j ∈ α, i ∈ j → f ‘ i ∈ f ‘ j)
    (hcof : ∀ x ∈ δ, ∃ i ∈ α, x ∈ f ‘ i) :
    internalCofinality δ = internalCofinality α := by
  let := IsFunction.of_mem hf
  have hmono : ∀ i ∈ α, ∀ j ∈ α, i ⊆ j → f ‘ i ⊆ f ‘ j := by
    intro i hi j hj hij
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem (function_value_mem hf hj)
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ (hinc i hi j hj hij)
  have hcf : IsCofinalMap δ α f := by
    refine ⟨hf, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcof x hx
    let := IsOrdinal.of_mem (function_value_mem hf hi)
    exact ⟨i, hi, IsOrdinal.toIsTransitive.transitive _ hxi⟩
  apply SetTheory.subset_antisymm
  · obtain ⟨g, hg⟩ := cofinalMap_exists α
    exact internalCofinality_minimal (monotone_cofinalMap_compose hcf hg hmono)
  · let R : V → V → Prop := fun x i ↦ i ∈ α ∧ x ∈ f ‘ i
    have hR : ℒₛₑₜ-relation R := by unfold R; definability
    let I := leastOrdinalOrZero R hR
    have hI : ℒₛₑₜ-function₁ I := by unfold I; definability
    have hspec (x : V) (hx : x ∈ δ) : I x ∈ α ∧ x ∈ f ‘ (I x) := by
      obtain ⟨i, hi, hxi⟩ := hcof x hx
      exact (leastOrdinalOrZero_spec R hR x ⟨i, IsOrdinal.of_mem hi, hi, hxi⟩).2.1
    obtain ⟨g, hg⟩ := cofinalMap_exists δ
    let H := definableGraph (internalCofinality δ) (fun j ↦ I (g ‘ j)) (by definability)
    have hH : H ∈ α ^ internalCofinality δ :=
      definableGraph_mem_function_of_mapsTo _ _ _ _
        (fun j hj ↦ (hspec _ (function_value_mem hg.1 hj)).1)
    apply internalCofinality_minimal (f := H)
    refine ⟨hH, ?_⟩
    intro i hi
    let := IsOrdinal.of_mem hi
    obtain ⟨j, hj, hbound⟩ := hg.2 (f ‘ i) (function_value_mem hf hi)
    have hs := hspec _ (function_value_mem hg.1 hj)
    let := IsOrdinal.of_mem hs.1
    refine ⟨j, hj, ?_⟩
    rw [show H ‘ j = I (g ‘ j) from value_definableGraph _ _ _ hj]
    rcases IsOrdinal.subset_or_supset i (I (g ‘ j)) with h | h
    · exact h
    rcases IsOrdinal.subset_iff.mp h with he | hlt
    · rw [he]
    have hfi : IsOrdinal (f ‘ i) := IsOrdinal.of_mem (function_value_mem hf hi)
    have hfk : IsOrdinal (f ‘ (I (g ‘ j))) := IsOrdinal.of_mem (function_value_mem hf hs.1)
    let := hfi
    let := hfk
    have hki : f ‘ (I (g ‘ j)) ∈ f ‘ i := hinc _ hs.1 i hi hlt
    have hkg : f ‘ (I (g ‘ j)) ∈ g ‘ j := hbound _ hki
    exact False.elim (mem_irrefl _ (IsOrdinal.toIsTransitive.transitive _ hs.2 _ hkg))

end ZFVP
