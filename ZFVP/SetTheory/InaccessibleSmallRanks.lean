import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.CofinalityCardinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.small_cardinal_bound (hAC : InternalChoice V) {κ D : V}
    (hκ : IsChoicelessInaccessible κ) (hD : D ∈ hierarchy κ) :
    ∃ lam ∈ κ, IsInitialOrdinal lam ∧ D ≤# lam := by
  let := hκ.1
  have hwo := wellOrderable_of_internalChoice hAC D
  have hlam := wellOrderedCardinal_initial hwo
  let := hlam.1
  have he := wellOrderedCardinal_cardEQ hwo
  refine ⟨wellOrderedCardinal D, ?_, hlam, he.2⟩
  by_contra hn
  have hle : κ ⊆ wellOrderedCardinal D := by
    rcases IsOrdinal.mem_trichotomy (wellOrderedCardinal D) κ with h | h | h
    · exact (hn h).elim
    · exact h ▸ subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ h
  obtain ⟨f, hf, hr⟩ := surjection_of_injection ((cardLE_of_subset hle).trans he.1)
    (show IsNonempty κ from ⟨ω, hκ.2.1⟩)
  exact hκ.no_rank_cofinalMap hD
    (cofinalMap_precompose_surjection (identity_isCofinalMap κ) hf hr)

end ZFVP
