import ZFVP.ModelTheory.TransitiveZFIterationHistory
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationHistory_val_of_previous (θ : SetDomain U)
    (h : ∀ i ∈ θ, (woodinIterationRec i).val = woodinIterationRec i.val) :
    (woodinIterationHistory θ).val = woodinIterationHistory θ.val := by
  unfold woodinIterationHistory
  exact definableGraph_val U θ _ _ _ _ h

theorem woodinIterationPrefixes_val_of_previous (θ : SetDomain U)
    (h : ∀ i ∈ θ, (woodinIterationRec i).val = woodinIterationRec i.val) :
    (woodinIterationPrefix θ).val = woodinIterationPrefix θ.val ∧
      (woodinIterationCardinalPrefix θ).val = woodinIterationCardinalPrefix θ.val := by
  constructor
  · unfold woodinIterationPrefix
    rw [forcingIterationCodeUnion_val, woodinHistoryCodes_val, woodinIterationHistory_val_of_previous U θ h]
  · unfold woodinIterationCardinalPrefix
    rw [woodinHistoryCardinalUnion_val, woodinHistoryCardinals_val, woodinIterationHistory_val_of_previous U θ h]
end TransitiveZF
end ZFVP
