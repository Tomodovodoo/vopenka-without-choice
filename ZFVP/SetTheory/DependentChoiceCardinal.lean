import ZFVP.SetTheory.DependentChoiceCofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Ordinal dependent choice depends only on the size of the ordinal. -/
theorem InternalDependentChoiceAt.of_cardLE {κ η : V} [IsOrdinal κ] [IsOrdinal η]
    (hκ : InternalDependentChoiceAt κ) (hηκ : η ≤# κ) : InternalDependentChoiceAt η := by
  classical
  by_cases hAC : InternalChoice V
  · exact dependentChoiceAt_of_internalChoice hAC η
  by_contra hη
  obtain ⟨μ, hμ, _⟩ := leastDependentChoiceFailure_existsUnique hAC
  let := hμ.1
  have hμη : μ ⊆ η := hμ.2.2 η inferInstance hη
  have hμκ : μ ⊆ κ := (initialOrdinal_cardLE_iff hμ.regular.1).mp
    ((cardLE_of_subset hμη).trans hηκ)
  exact hμ.2.1 (hκ.downward hμκ)

theorem dependentChoiceAt_cardEQ_iff {κ η : V} [IsOrdinal κ] [IsOrdinal η]
    (h : κ ≋ η) : InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt η :=
  ⟨fun hκ ↦ hκ.of_cardLE h.2, fun hη ↦ hη.of_cardLE h.1⟩

end ZFVP
