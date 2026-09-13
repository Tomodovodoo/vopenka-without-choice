import ZFVP.SetTheory.UltrafilterFibers
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.SetTheory.BooleanCompletionValues

/-! Since a measurable cardinal is a strong limit, the power set of a set of size below `κ` has
size below `κ`; consequently the Boolean completion of a sub-collapse `Coll(ω, <ξ)`, `ξ < κ`,
has size below `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc in
/-- The power set of a set of size below a measurable `κ` has size below `κ`. -/
theorem power_small_of_measurable {X μ : V} (hμ : μ ∈ κ) (hX : X ≤# μ) :
    ∃ ν ∈ κ, ℘ X ≤# ν := by
  have hpow : ℘ X ≤# ℘ μ := power_cardLE_of_cardLE hX
  have hwo : IsWellOrderable (℘ μ) := wellOrderable_of_internalChoice hAC _
  obtain ⟨ν, hν, hcard⟩ := (wellOrderable_iff_cardLE_ordinal (℘ μ)).mp hwo
  have : IsOrdinal ν := hν
  have hinit := wellOrderedCardinal_initial hwo
  have hceq := wellOrderedCardinal_cardEQ hwo
  have : IsOrdinal (wellOrderedCardinal (℘ μ)) := hinit.1
  -- the cardinal of `℘ μ` lies below `κ`
  rcases IsOrdinal.subset_or_supset (α := κ) (β := wellOrderedCardinal (℘ μ)) with h | h
  · exfalso
    exact measurable_not_cardLE_power hU hc hμ ((cardLE_of_subset h).trans hceq.1)
  · rcases IsOrdinal.subset_iff.mp h with h | h
    · exfalso
      exact measurable_not_cardLE_power hU hc hμ (h ▸ hceq.1)
    · exact ⟨wellOrderedCardinal (℘ μ), h, hpow.trans hceq.2⟩

include hAC hU hc hω hκ in
/-- The Boolean completion of a sub-collapse has size below `κ`. -/
theorem levyBooleanConditions_small {ξ : V} (hξ : ξ ∈ κ) :
    ∃ ν ∈ κ, booleanConditions (levyCollapse ξ) (levyOrder ξ) ≤# ν := by
  obtain ⟨μ, hμ, hsmall⟩ := levyCollapse_small hAC hU hc hω hκ hξ
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hμ hsmall
  refine ⟨ν, hν, (cardLE_of_subset ?_).trans hpow⟩
  intro A hA
  exact mem_power_iff.mpr (booleanConditions_regular hA).1

end

end ZFVP
