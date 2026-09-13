import ZFVP.SetTheory.ForcingAutomorphisms

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternalPermutation (I π : V) : Prop := π ∈ I ^ I ∧ Injective π ∧ range π = I

instance isInternalPermutation_definable : ℒₛₑₜ-relation[V] IsInternalPermutation := by
  unfold IsInternalPermutation
  definability

noncomputable def internalPermutations (I : V) : V :=
  {π ∈ I ^ I ; Injective π ∧ range π = I}

theorem mem_internalPermutations (I π : V) :
    π ∈ internalPermutations I ↔ IsInternalPermutation I π := by
  simp only [internalPermutations, mem_sep_iff, IsInternalPermutation]

instance internalPermutations_definable : ℒₛₑₜ-function₁[V] internalPermutations := by
  have h : ℒₛₑₜ-relation[V] (fun G I ↦ ∀ π, π ∈ G ↔ IsInternalPermutation I π) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalPermutations (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_internalPermutations]

theorem internalPermutation_iff_emptyOrder (I π : V) :
    IsInternalPermutation I π ↔ IsForcingAutomorphism I ∅ π := by
  constructor
  · rintro ⟨hf, hi, hr⟩
    exact ⟨hf, hi, hr, fun _ _ _ _ ↦ by simp⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem internalPermutation_identity (I : V) : IsInternalPermutation I (identity I) :=
  (internalPermutation_iff_emptyOrder I _).mpr (forcingAutomorphism_identity I ∅)

theorem IsInternalPermutation.comp {I π ρ : V}
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ) :
    IsInternalPermutation I (compose π ρ) :=
  (internalPermutation_iff_emptyOrder I _).mpr
    (forcingAutomorphism_compose ((internalPermutation_iff_emptyOrder I π).mp hπ)
      ((internalPermutation_iff_emptyOrder I ρ).mp hρ))

theorem IsInternalPermutation.inv {I π : V} (hπ : IsInternalPermutation I π) :
    IsInternalPermutation I (converseGraph π) :=
  (internalPermutation_iff_emptyOrder I _).mpr
    (forcingAutomorphism_inverse ((internalPermutation_iff_emptyOrder I π).mp hπ))

theorem IsInternalPermutation.surjective {I π : V} (hπ : IsInternalPermutation I π)
    {i : V} (hi : i ∈ I) : ∃ j ∈ I, π ‘ j = i :=
  forcingAutomorphism_surjective ((internalPermutation_iff_emptyOrder I π).mp hπ) i hi

theorem IsInternalPermutation.inv_value {I π i : V} (hπ : IsInternalPermutation I π)
    (hi : i ∈ I) : (converseGraph π) ‘ (π ‘ i) = i :=
  converseGraph_value_value hπ.1 hπ.2.1 hi

theorem IsInternalPermutation.value_inv {I π i : V} (hπ : IsInternalPermutation I π)
    (hi : i ∈ I) : π ‘ ((converseGraph π) ‘ i) = i :=
  value_converseGraph_value hπ.1 hπ.2.1 (hπ.2.2.symm ▸ hi)

end ZFVP
