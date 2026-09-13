import ZFVP.ModelTheory.ForcingNameActionRank
import ZFVP.SetTheory.InaccessibleFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_mem_hierarchy_of_low_condition_values {η P π τ : V}
    (hη : IsChoicelessInaccessible η)
    (hπ : ∀ p ∈ P, π ‘ p ∈ hierarchy η)
    (hτ : τ ∈ hierarchy η) (hn : IsForcingName P τ) :
    nameAction π τ ∈ hierarchy η := by
  let := hη.1
  have hs := hη.rankCriterion.2.2.1
  have hall : ∀ t ∈ namesBelow P η, nameAction π t ∈ hierarchy η := by
    apply projectedRank_induction (namesBelow P η) (fun x : V ↦ x) (by definability)
      (fun t ↦ nameAction π t ∈ hierarchy η) (by definability)
    intro t ht ih
    obtain ⟨htV, htN⟩ := mem_namesBelow_iff _ _ _ |>.mp ht
    let F := fun z : V ↦ ⟨nameAction π (kpair.π₁ z), π ‘ (kpair.π₂ z)⟩ₖ
    have hF : ℒₛₑₜ-function₁[V] F := by unfold F; definability
    have hmaps : definableGraph t F hF ∈ hierarchy η ^ t := by
      apply definableGraph_mem_function_of_mapsTo
      intro z hz
      obtain ⟨σ, p, hp, rfl⟩ := htN t (mem_nameClosure_self t) z hz
      have hσ := namesBelow_closed P η t ht σ (mem_domain_of_kpair_mem hz)
      simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using
        kpair_mem_hierarchy_limit hs (ih σ hσ (rank_subname_lt hz)) (hπ p hp)
    have hr := hη.rankCriterion.2.2.2.range_mem hs htV hmaps
    apply subset_mem_hierarchy_limit hs hr
    intro z hz
    obtain ⟨σ, p, hp, rfl⟩ := (mem_nameAction_iff htN π z).mp hz
    rw [range_definableGraph, repl_spec]
    exact ⟨⟨σ, p⟩ₖ, hp, by simp [F]⟩
  exact hall τ ((mem_namesBelow_iff _ _ _).mpr ⟨hτ, hn⟩)

theorem nameAction_mem_hierarchy_of_low_target {η P Q π τ : V}
    (hη : IsChoicelessInaccessible η) (hπ : π ∈ Q ^ P)
    (hQ : Q ⊆ hierarchy η) (hτ : τ ∈ hierarchy η) (hn : IsForcingName P τ) :
    nameAction π τ ∈ hierarchy η :=
  nameAction_mem_hierarchy_of_low_condition_values hη
    (fun _ hp ↦ hQ _ (function_value_mem hπ hp)) hτ hn

end ZFVP

