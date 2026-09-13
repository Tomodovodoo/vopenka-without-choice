import ZFVP.ModelTheory.TransitiveZFNormalizedRecodedCode
import ZFVP.ModelTheory.WoodinSparseRecursion
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Agreement of the history graph follows from agreement at its indices. -/
theorem woodinSparseRecodingHistory_val_of_stages (θ : SetDomain U)
    (h : ∀ i : SetDomain U, i ∈ θ →
      (woodinSparseRecodingRec i).val = woodinSparseRecodingRec i.val) :
    (woodinSparseRecodingHistory θ).val = woodinSparseRecodingHistory θ.val := by
  unfold woodinSparseRecodingHistory
  exact definableGraph_val U θ _ _ _ _ h

end TransitiveZF
end ZFVP
