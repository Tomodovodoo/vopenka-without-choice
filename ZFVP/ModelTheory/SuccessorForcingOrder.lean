import ZFVP.ModelTheory.SuccessorForcingColumns
import ZFVP.SetTheory.ForcingOrderExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successor_orderedColumn {θ P R π E k Q S t one : V}
    (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
    (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t) :
    IsOrderedSplitForcingColumn θ P R (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S t)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k)
      (successorSectionColumn θ P E k t) := by
  have base {a : V} (ha : a ∈ twoStepConditions (P ‘ k) (R ‘ k) Q t) : kpair.π₁ a ∈ P ‘ k := by
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    simpa only [kpair.π₁_kpair] using hp
  refine ⟨twoStep_preorder (o.preorder k hk) htop hQ, ?_, ?_⟩
  · intro i hi a ha b hb hab
    rw [successorProjectionColumn_value hi ha, successorProjectionColumn_value hi hb]
    exact o.projMono i hi k hk (hmax i hi) _ (base ha) _ (base hb)
      ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hab).2.2.1
  · intro i hi a ha b hb
    rw [successorProjectionColumn_value hi ha, successorSectionColumn_value hi hb,
      twoStep_below_section (o.preorder k hk) htop hQ ha
        (h.secMaps i hi k hk (hmax i hi) b hb)]
    exact o.below i hi k hk (hmax i hi) _ (base ha) b hb

end ZFVP
