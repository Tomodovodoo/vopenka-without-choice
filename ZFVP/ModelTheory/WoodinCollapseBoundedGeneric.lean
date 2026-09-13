import ZFVP.ModelTheory.ForcingPredense
import ZFVP.SetTheory.WoodinCollapsePredense

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_generic_bounded_dense_family {κ δ γ : V} {G : Set V}
    (hδ : IsChoicelessInaccessible δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ)
    (hγ : γ ∈ δ) (D : V → V) (hD : ℒₛₑₜ-function₁ D)
    (hd : ∀ i ∈ γ, ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (D i))
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∃ β ∈ δ, IsOrdinal β ∧ ∀ i ∈ γ, ∃ q ∈ G, q ∈ D i ∧ q ∈ hierarchy β := by
  obtain ⟨β, hβ, ho, hb⟩ := woodinCollapse_bounded_predense_family hδ hκ hκδ hγ D hD (by
    intro i hi
    refine ⟨(hd i hi).1, ?_⟩
    intro p hp
    obtain ⟨q, hq, hqp⟩ := (hd i hi).2 p hp
    exact ⟨q, hq, ((pair_mem_reverseInclusionOrder _ _ _).mp hqp).2.2⟩)
  refine ⟨β, hβ, ho, ?_⟩
  intro i hi
  let E := D i ∩ hierarchy β
  have hE : E ⊆ woodinCollapse κ δ := fun q hq ↦ (hd i hi).1 q (mem_inter_iff.mp hq).1
  obtain ⟨q, hqG, hqE⟩ := externalForcingGeneric_meets_predense hG hE (by
    intro p hp
    obtain ⟨q, hq, hqV, r, hr, hpr, hqr⟩ := hb i hi p hp
    exact ⟨q, mem_inter_iff.mpr ⟨hq, hqV⟩, r, hr,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hp, hpr⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, (hd i hi).1 q hq, hqr⟩⟩)
  exact ⟨q, hqG, mem_inter_iff.mp hqE⟩

end ZFVP
