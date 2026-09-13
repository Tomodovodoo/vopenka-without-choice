import ZFVP.SetTheory.FinitePermutationExtension

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Preserve prescribed permutation values on `D` while moving `B` outside a finite target.
The overlap of `D` and `B` must lie in the protected set `C`. -/
theorem finite_permutation_fresh_extension {B C D T a : V}
    (hB : IsInternallyFinite B) (hBω : B ⊆ (ω : V))
    (hC : IsInternallyFinite C) (hCω : C ⊆ (ω : V))
    (hD : IsInternallyFinite D) (hDω : D ⊆ (ω : V))
    (hT : IsInternallyFinite T) (hTω : T ⊆ (ω : V))
    (hfresh : ∀ i ∈ D, i ∈ B → i ∈ C)
    (ha : IsInternalPermutation (ω : V) a) (hafix : ∀ i ∈ C, a ‘ i = i) :
    ∃ b, IsInternalPermutation (ω : V) b ∧ (∀ i ∈ C, b ‘ i = i) ∧
      (∀ i ∈ D, b ‘ i = a ‘ i) ∧ ∀ i ∈ B, i ∉ C → b ‘ i ∉ T := by
  let A := {i ∈ B ; i ∉ C}
  let K := repl (fun i ↦ a ‘ i) (by definability) D ∪ C
  let X := repl (fun i ↦ a ‘ i) (by definability) A
  have hA : IsInternallyFinite A := internallyFinite_subset hB sep_subset
  have hK : IsInternallyFinite K := internallyFinite_union (internallyFinite_repl _ _ hD) hC
  have hKω : K ⊆ (ω : V) := by
    intro i hi
    rcases mem_union_iff.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := (repl_spec _).mp hi
      exact function_value_mem ha.1 (hDω j hj)
    · exact hCω i hi
  have hX : IsInternallyFinite X := internallyFinite_repl _ _ hA
  have hXω : X ⊆ (ω : V) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := (repl_spec _).mp hi
    exact function_value_mem ha.1 (hBω j (mem_sep_iff.mp hj).1)
  have hXK : ∀ i ∈ X, i ∉ K := by
    intro i hi hiK
    obtain ⟨j, hj, rfl⟩ := (repl_spec _).mp hi
    obtain ⟨hjB, hjC⟩ := mem_sep_iff.mp hj
    rcases mem_union_iff.mp hiK with hiD | hiC
    · obtain ⟨k, hk, he⟩ := (repl_spec _).mp hiD
      have hjk := injective_value_eq ha.1 ha.2.1 (hBω j hjB) (hDω k hk) he
      exact hjC (hfresh j (hjk.symm ▸ hk) hjB)
    · have hej := injective_value_eq ha.1 ha.2.1 (hBω j hjB) (hCω _ hiC) (hafix _ hiC).symm
      exact hjC (hej.symm ▸ hiC)
  obtain ⟨ρ, hρ, hρfix, hmove⟩ := exists_permutation_moving_fixing hK hKω hX hXω hT hTω hXK
  refine ⟨compose a ρ, ha.comp hρ, ?_, ?_, ?_⟩
  · intro i hi
    rw [value_compose_of_mem_function ha.1 hρ.1 (hCω i hi), hafix i hi]
    exact hρfix i (mem_union_iff.mpr (Or.inr hi))
  · intro i hi
    rw [value_compose_of_mem_function ha.1 hρ.1 (hDω i hi)]
    exact hρfix _ (mem_union_iff.mpr (Or.inl ((repl_spec _).mpr ⟨i, hi, rfl⟩)))
  · intro i hi hiC
    rw [value_compose_of_mem_function ha.1 hρ.1 (hBω i hi)]
    exact hmove _ ((repl_spec _).mpr ⟨i, mem_sep_iff.mpr ⟨hi, hiC⟩, rfl⟩)

/-- Move the unprotected part of `D` away from `B ∪ T`, fixing `C` and all coordinates of
`B ∪ T` outside `D`. -/
theorem finite_permutation_move_fresh_fixing_complement {B C D T : V}
    (hB : IsInternallyFinite B) (hBω : B ⊆ (ω : V))
    (hC : IsInternallyFinite C) (hCω : C ⊆ (ω : V))
    (hD : IsInternallyFinite D) (hDω : D ⊆ (ω : V))
    (hT : IsInternallyFinite T) (hTω : T ⊆ (ω : V)) :
    ∃ b, IsInternalPermutation (ω : V) b ∧ (∀ i ∈ C, b ‘ i = i) ∧
      (∀ i ∈ B ∪ T, i ∉ D → b ‘ i = i) ∧
      ∀ i ∈ D, i ∉ C → b ‘ i ∉ B ∪ T := by
  let K := {i ∈ B ∪ T ; i ∉ D} ∪ C
  let X := {i ∈ D ; i ∉ C}
  have hBT : IsInternallyFinite (B ∪ T) := internallyFinite_union hB hT
  have hBTω : B ∪ T ⊆ (ω : V) :=
    fun i hi ↦ (mem_union_iff.mp hi).elim (hBω i) (hTω i)
  have hK : IsInternallyFinite K :=
    internallyFinite_union (internallyFinite_subset hBT sep_subset) hC
  have hKω : K ⊆ (ω : V) := by
    intro i hi
    rcases mem_union_iff.mp hi with hi | hi
    · exact hBTω i (mem_sep_iff.mp hi).1
    · exact hCω i hi
  have hX : IsInternallyFinite X := internallyFinite_subset hD sep_subset
  have hXω : X ⊆ (ω : V) := fun i hi ↦ hDω i (mem_sep_iff.mp hi).1
  have hXK : ∀ i ∈ X, i ∉ K := by
    intro i hi hiK
    obtain ⟨hiD, hiC⟩ := mem_sep_iff.mp hi
    rcases mem_union_iff.mp hiK with hiK | hiK
    · exact (mem_sep_iff.mp hiK).2 hiD
    · exact hiC hiK
  obtain ⟨b, hb, hfix, hmove⟩ := exists_permutation_moving_fixing hK hKω hX hXω hBT hBTω hXK
  exact ⟨b, hb, fun i hi ↦ hfix i (mem_union_iff.mpr (Or.inr hi)),
    fun i hi hiD ↦ hfix i (mem_union_iff.mpr (Or.inl (mem_sep_iff.mpr ⟨hi, hiD⟩))),
    fun i hi hiC ↦ hmove i (mem_sep_iff.mpr ⟨hi, hiC⟩)⟩

end ZFVP

