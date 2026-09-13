import ZFVP.ModelTheory.SymmetricDependentChoice
import ZFVP.ModelTheory.CountableCohenModel
import ZFVP.SetTheory.OrdinalDependentChoiceAC

/-! Dependent choice in the countable-support Cohen model at omega_1: the forcing is
closed under descending omega-sequences and the countable-stabilizer filter is closed
under countable intersections, so Karagila's lemma applies over a choice ground. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace OmegaOneCohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
    (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) G)

theorem model_dependentChoice (hAC : InternalChoice V) :
    InternalDependentChoice (omegaOneCohenContext G hG).Model := by
  have hCC : InternalCountableChoice V := countableChoice_of_internalChoice hAC
  apply (omegaOneCohenContext G hG).dependentChoice (dependentChoice_of_internalChoice hAC)
  · exact countablePartialFunctions_closedAt hCC inferInstance (subset_refl _)
  · intro H hH hd hmem
    let := hH
    exact countableStabilizerFilter_countable_inter hCC hd hmem

end OmegaOneCohenModel
end ZFVP
