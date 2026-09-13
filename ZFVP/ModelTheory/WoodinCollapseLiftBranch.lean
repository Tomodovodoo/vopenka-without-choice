import ZFVP.ModelTheory.WoodinCollapseLiftDomain

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

variable {κ δ : V} (hκ : IsRegularCardinal κ) [IsOrdinal δ] {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

set_option maxHeartbeats 1200000 in
theorem lifted_branch {A : ForcingContext V} {ρ ε e π : V}
    (L : SuccessorRankLiftData A (woodinCollapseContext hκ δ G hG) ρ ε e)
    (hπ : IsForcingRetraction A.P A.R (woodinCollapse κ δ) (woodinCollapseOrder κ δ) π)
    (hAG : ∀ p, p ∈ A.G ↔ p ∈ G ∧ p ∈ A.P)
    (hone : A.one = ∅) (heone : e ‘ A.one = ∅)
    (hρδ : ρ ∈ δ) (hκV : κ ∈ hierarchy ρ)
    (hfix : ∀ α ∈ κ, e ‘ α = α) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    {X R : (woodinCollapseContext hκ δ G hG).Model}
    (hX : X ∈ domain (L.graph hπ)) (hR : R ∈ domain (L.graph hπ))
    (hserial : ∀ s ∈ shorterSequences ((woodinCollapseContext hκ δ G hG).check κ) ((L.graph hπ) ‘ X),
      ∃ x ∈ (L.graph hπ) ‘ X, ⟨s, x⟩ₖ ∈ (L.graph hπ) ‘ R) :
    ∃ f, IsDependentChoicePath ((L.graph hπ) ‘ X) ((L.graph hπ) ‘ R)
      ((woodinCollapseContext hκ δ G hG).check κ) f := by
  let S := woodinCollapseContext hκ δ G hG
  let := hκ.1.1
  let := L.source_correct.ordinal
  have hD := L.graph_boundedElementary hπ hAG
  apply hD.dependentChoicePath hX hR (L.check_mem_graph_domain hπ hone hκV) ?_ ?_
    (liftedDomain_wellOrderable hκ hG L hπ hρδ hX) hserial
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff κ α).mp hα
    have haV := (hierarchy_transitive ρ).mem_trans ha hκV
    rw [L.graph_check hπ hAG hone heone haV, hfix a ha]
  · intro α hα s hs
    obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff κ α).mp hα
    let := IsOrdinal.of_mem ha
    apply L.function_mem_graph_domain_of_closed hπ hAG hone
      ((hierarchy_transitive ρ).mem_trans ha hκV) (hDC a ha) ?_ hX hs
    intro β hβ hβα
    let := hβ
    exact woodinCollapse_closedBelow hκ hDC δ β (ordinal_mem_of_subset_mem hβα ha)

end WoodinCollapseModel
end ZFVP
