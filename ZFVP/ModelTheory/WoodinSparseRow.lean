import ZFVP.ModelTheory.WoodinSparseHistory
import ZFVP.ModelTheory.WoodinRecodingConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinSparseRow (θ r : V) : Prop :=
  IsWoodinRecodedRow θ r ∧
  (∀ p ∈ kpair.π₁ r, IsSparseFunctionOn (succ (woodinSourceIndex θ)) p) ∧
  (kpair.π₂ (kpair.π₂ r)) ‘ ((forcingCodet (woodinNormalizedStageCode θ)) ‘ θ) = ∅ ∧
  (∀ i ∈ θ, ∀ p ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ,
    ((kpair.π₂ (kpair.π₂ r)) ‘ p) ↾ (succ (woodinSourceIndex i)) =
      (kpair.π₂ (kpair.π₂ (woodinSparseRecodingRec i))) ‘
        (((forcingCodeπ (woodinNormalizedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ p)) ∧
  (∀ i ∈ θ, ∀ p ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ i,
    (kpair.π₂ (kpair.π₂ r)) ‘ (((forcingCodeE (woodinNormalizedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      (kpair.π₂ (kpair.π₂ (woodinSparseRecodingRec i))) ‘ p)

instance isWoodinSparseRow_definable : ℒₛₑₜ-relation[V] IsWoodinSparseRow := by
  unfold IsWoodinSparseRow
  definability

end ZFVP
