import ZFVP.SetTheory.HartogsRegular
import ZFVP.SetTheory.OrdinalPairing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLimitOfRegularCardinals (κ : V) : Prop :=
  IsOrdinal κ ∧ (ω : V) ⊆ κ ∧ ∀ β ∈ κ, ∃ ρ ∈ κ, IsRegularCardinal ρ ∧ β ∈ ρ

def limitOfRegularCardinalsFormula : SetTheorySemisentence 1 :=
  f“κ. !IsOrdinal.dfn κ ∧ !isω ⊆ κ ∧ ∀ β ∈ κ, ∃ ρ ∈ κ, !regularCardinalFormula ρ ∧ β ∈ ρ”

instance limitOfRegularCardinalsFormula_defined :
    ℒₛₑₜ-predicate[V] IsLimitOfRegularCardinals via limitOfRegularCardinalsFormula :=
  ⟨fun v ↦ by simp [limitOfRegularCardinalsFormula, IsLimitOfRegularCardinals]⟩

instance isLimitOfRegularCardinals_definable : ℒₛₑₜ-predicate[V] IsLimitOfRegularCardinals :=
  limitOfRegularCardinalsFormula_defined.to_definable

theorem hartogsNumber_regular_of_regular {κ : V} (hκ : IsRegularCardinal κ)
    (hDC : InternalDependentChoiceAt κ) : IsRegularCardinal (hartogsNumber κ) := by
  let := hκ.1.1
  exact hartogsNumber_regular_of_square hκ.2.1 (regularCardinal_square_cardLE hκ) hDC

theorem hartogsNumber_regular_of_limit_regulars {κ : V} (hκ : IsLimitOfRegularCardinals κ)
    (hDC : InternalDependentChoiceAt κ) : IsRegularCardinal (hartogsNumber κ) := by
  let := hκ.1
  exact hartogsNumber_regular_of_square hκ.2.1 (limit_regularCardinals_square_cardLE hκ.2.2) hDC

theorem dependentChoiceBelow_hartogsNumber {κ : V} [IsOrdinal κ]
    (hDC : InternalDependentChoiceAt κ) :
    ∀ α ∈ hartogsNumber κ, InternalDependentChoiceAt α := by
  intro α hα
  let := IsOrdinal.of_mem hα
  exact hDC.of_cardLE (cardLE_of_mem_hartogsNumber hα)

end ZFVP
