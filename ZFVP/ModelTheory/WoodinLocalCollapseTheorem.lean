import ZFVP.ModelTheory.WoodinSupercompactRestoration
import ZFVP.SetTheory.WoodinDependentChoiceFailure
import ZFVP.SetTheory.WoodinCollapseMembershipFormula
import ZFVP.SetTheory.WoodinCollapseChainCondition
import ZFVP.SetTheory.WoodinCollapseDisplacement
import ZFVP.SetTheory.WoodinCollapseHomogeneity
import ZFVP.SetTheory.WoodinCollapseDirectedClosure
import ZFVP.SetTheory.WoodinCollapseDistributivity
import ZFVP.SetTheory.SigmaTwoWoodinCollapse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The local collapse conclusion, with the original reverse-inclusion order.
Membership complexity and the graph of the whole carrier are separate claims. -/
structure WoodinLocalCollapseConclusion (κ δ : V) : Prop where
  poset : IsForcingPoset (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
  top : IsForcingTop (woodinCollapse κ δ) (woodinCollapseOrder κ δ) ∅
  membership : ∀ p, sigmaOneWoodinCollapseMembershipFormula.Evalb ![p, κ, δ] ↔ p ∈ woodinCollapse κ δ
  membership_complexity : IsSigmaFormula 1 sigmaOneWoodinCollapseMembershipFormula
  carrier_graph : ∀ P, sigmaTwoWoodinCollapseFormula.Evalb ![P, κ, δ] ↔ P = woodinCollapse κ δ
  carrier_complexity : IsSigmaFormula 2 sigmaTwoWoodinCollapseFormula
  homogeneous : ∀ p ∈ woodinCollapse κ δ, ∀ q ∈ woodinCollapse κ δ,
    ∃ π, IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ) π ∧
      ∃ r ∈ woodinCollapse κ δ,
        ⟨r, π ‘ p⟩ₖ ∈ woodinCollapseOrder κ δ ∧ ⟨r, q⟩ₖ ∈ woodinCollapseOrder κ δ
  cones : ∀ p ∈ woodinCollapse κ δ, ∀ q ∈ woodinCollapse κ δ,
    ∃ f, IsForcingIsomorphism (woodinCollapseCone κ δ p)
      (reverseInclusionOrder (woodinCollapseCone κ δ p))
      (woodinCollapseCone κ δ q) (reverseInclusionOrder (woodinCollapseCone κ δ q)) f
  directed_closed : ∀ γ ∈ κ,
    IsForcingDirectedClosedAt (woodinCollapse κ δ) (woodinCollapseOrder κ δ) γ
  closed : IsForcingClosedBelow (woodinCollapse κ δ) (woodinCollapseOrder κ δ) κ
  successor_chain_bound : ¬hartogsNumber δ ≤# woodinCollapse κ δ
  restoration : ∀ p ∈ woodinCollapse κ δ,
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ])

/-- All local obligations follow from regularity, the available dependent choice,
and Woodin supercompactness. No embedding-lift or restoration invariant is an input. -/
theorem woodinLocalCollapseConclusion {κ δ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsWoodinSupercompact δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) : WoodinLocalCollapseConclusion κ δ := by
  let := hδ.1.1
  exact {
    poset := woodinCollapse_poset κ δ
    top := woodinCollapse_top (hκ.2.1 ∅ (by simp)) δ
    membership := fun p ↦ eval_sigmaOneWoodinCollapseMembershipFormula p κ δ
    membership_complexity := sigmaOneWoodinCollapseMembershipFormula_sigmaOne
    carrier_graph := fun P ↦ (eval_sigmaTwoWoodinCollapseFormula P κ δ).trans ⟨And.right, fun h ↦ ⟨hδ.1.1, h⟩⟩
    carrier_complexity := sigmaTwoWoodinCollapseFormula_sigmaTwo
    homogeneous := fun _ hp _ hq ↦ woodinCollapse_weak_homogeneous hκ hp hq
    cones := fun _ hp _ hq ↦ woodinCollapse_cone_isomorphic hκ hp hq
    directed_closed := fun γ hγ ↦ woodinCollapse_directedClosedAt hκ hγ (hDC γ hγ)
    closed := woodinCollapse_closedBelow hκ hDC δ
    successor_chain_bound := woodinCollapse_no_successor_injection hδ.inaccessible
      (IsOrdinal.toIsTransitive.transitive _ hκδ)
    restoration := fun _ hp ↦ woodinSupercompact_collapse_forces_restoration hκ hδ hκδ hDC hp }

/-- The least failure used to begin the iteration exists uniquely, is regular,
lies below every Woodin supercompact, and its collapse has the full local conclusion. -/
theorem woodinLeastFailure_localCollapse {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃! κ, IsLeastDependentChoiceFailure κ ∧ IsRegularCardinal κ ∧ κ ∈ δ ∧
      (∀ α ∈ κ, InternalDependentChoiceAt α) ∧ ¬InternalDependentChoiceAt κ ∧
      WoodinLocalCollapseConclusion κ δ := by
  obtain ⟨κ, hκ, hu⟩ := leastDependentChoiceFailure_existsUnique hAC
  refine ⟨κ, ⟨hκ, hκ.regular, hκ.lt_supercompact hδ, fun _ hα ↦ hκ.below hα,
    hκ.2.1, woodinLocalCollapseConclusion hκ.regular hδ (hκ.lt_supercompact hδ)
      (fun _ hα ↦ hκ.below hα)⟩, ?_⟩
  exact fun μ hμ ↦ hu μ hμ.1

end ZFVP
