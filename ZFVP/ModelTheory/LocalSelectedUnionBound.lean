import ZFVP.ModelTheory.ForcingLocalCanonicalName
import ZFVP.ModelTheory.ForcingSelectedUnion
import ZFVP.SetTheory.WoodinCollapseRank
import ZFVP.ModelTheory.ForcingSmallInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V)

theorem localCanonicalName_value {δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (τ : ForcingName A.P) (hτ : A.ofName τ ∈ hierarchy (A.check δ)) :
    A.ofName ⟨forcingLocalCanonicalName A.P A.R A.one δ p τ.val,
      forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ = A.ofName τ := by
  exact (A.restrictedName_value hp
    ⟨forcingCanonicalName A.P A.R A.one δ τ.val, forcingCanonicalName_isName _ _ _ _ _⟩).trans
      (A.canonicalName_value hδ hP τ hτ)

/-- Normalizing the union below a fixed root preserves its lower-bound value. -/
theorem localSelectedUnion_collapse_bound {C D H δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {κ α : A.Model}
    (hf : A.ofName f ∈ A.check D ^ α)
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ)
    (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hs : IsForcingDescending (woodinCollapse κ (A.check δ))
      (forcingSeparativeOrder (woodinCollapse κ (A.check δ)) (woodinCollapseOrder κ (A.check δ))) α
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC))) :
    let ν := forcingLocalCanonicalName A.P A.R A.one δ p
      (forcingSelectedUnion A.P A.R A.one C H f.val)
    let u := A.ofName ⟨ν, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    u ∈ woodinCollapse κ (A.check δ) ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i⟩ₖ ∈
        woodinCollapseOrder κ (A.check δ) := by
  dsimp only
  have hu := A.forcingSelectedUnion_collapse_bound hC hH f hf hκ hα hDC hs
  have hr := woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular hκδ hu.1
  rw [A.localCanonicalName_value hδ hP hp
    ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ hr]
  exact hu

theorem forcingSelectedUnion_value_empty {C D H : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {α : A.Model} (hf : A.ofName f ∈ A.check D ^ α)
    (he : ∀ i ∈ α,
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i = ∅) :
    A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val,
      forcingSelectedUnion_isName _ _ _ _ _ _⟩ = ∅ := by
  rw [A.forcingSelectedUnion_eq_union_range hC hH f hf]
  have hs := compose_function
    (compose_function hf ((A.check_function_iff H D C).mpr hH)) (A.evaluationGraph_mem_function C hC)
  let := IsFunction.of_mem hs
  apply subset_empty_iff_eq_empty.mp
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
  obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
  have hi := (domain_eq_of_mem_function hs) ▸ mem_domain_of_kpair_mem hiy
  rw [← value_eq_of_kpair_mem hiy, he i hi] at hxy
  exact False.elim (not_mem_empty hxy)

end ForcingContext
end ZFVP
