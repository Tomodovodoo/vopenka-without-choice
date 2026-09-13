import ZFVP.ModelTheory.WoodinCollapseRankEnumeration
import ZFVP.ModelTheory.ForcingHierarchyAgreement
import ZFVP.SetTheory.WoodinCollapseDistributivity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace WoodinCollapseModel
variable {κ δ θ : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

/-- A collapse advances the rank-enumeration invariant by one ordinal step. -/
theorem hierarchy_enumeration_successor (hδ : IsRegularCardinal δ) (hκδ : κ ∈ δ)
    (hθ : θ ∈ δ) (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)
    (henum : ∀ α ∈ θ, ∃ γ ∈ κ, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α) :
    let A := woodinCollapseContext hκ δ G hG
    ∀ α ∈ A.check (succ θ), ∃ γ ∈ A.check δ, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α := by
  let := hκ.1.1
  let := hδ.1.1
  let := IsOrdinal.of_mem hθ
  let A := woodinCollapseContext hκ δ G hG
  change ∀ α ∈ A.check (succ θ), ∃ γ ∈ A.check δ, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := (A.mem_check_iff (succ θ) α).mp hα
  let := IsOrdinal.of_mem hβ
  have hβθ : β ⊆ θ := by
    rcases mem_succ_iff.mp hβ with rfl | hβθ
    · exact fun _ hx ↦ hx
    · exact IsOrdinal.toIsTransitive.transitive _ hβθ
  have hβδ : β ∈ δ := ordinal_mem_of_subset_mem hβθ hθ
  have heq : A.check (hierarchy β) = hierarchy (A.check β) :=
    A.check_hierarchy_of_closed hDC (woodinCollapse_closedBelow hκ hDC δ)
      (fun a ha ↦ henum a (hβθ a ha))
  rw [← heq]
  exact check_hierarchy_enumeration_below_upper hκ hG hδ hκδ hβδ

end WoodinCollapseModel
end ZFVP
