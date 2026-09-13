import ZFVP.ModelTheory.SuccessorForcingColumns
import ZFVP.SetTheory.ForcingTopExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successor_toppedColumn {θ P R π E t k Q S u : V}
    (h : IsToppedSplitForcingSystem θ P R π E t)
    (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k))
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S u) :
    IsToppedSplitForcingColumn θ t (twoStepConditions (P ‘ k) (R ‘ k) Q u)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S u)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q u) π k)
      (successorSectionColumn θ P E k u) ⟨t ‘ k, u⟩ₖ := by
  have ht := twoStep_top hR (h.top k hk) hQ
  refine ⟨ht, ?_, ?_⟩
  · intro i hi
    rw [successorProjectionColumn_value hi ht.1, kpair.π₁_kpair]
    exact h.projTop i hi k hk (hmax i hi)
  · intro i hi
    rw [successorSectionColumn_value hi (h.top i hi).1, h.secTop i hi k hk (hmax i hi)]

end ZFVP
