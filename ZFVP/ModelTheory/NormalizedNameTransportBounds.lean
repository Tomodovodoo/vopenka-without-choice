import ZFVP.ModelTheory.NormalizedTwoStepExtension
import ZFVP.ModelTheory.ForcingNameActionRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem suborderMap_mem_hierarchy {P N f γ : V} [IsOrdinal γ]
    (hγ : ∀ β ∈ γ, succ β ∈ γ) (hP : P ∈ hierarchy γ)
    (hN : N ⊆ P) (hf : f ∈ N ^ P) : f ∈ hierarchy γ :=
  subset_mem_hierarchy_limit hγ (prod_mem_hierarchy_limit hγ hP hP)
    (subset_prod_of_mem_function (mem_function_of_mem_function_of_subset hf hN))

theorem suborderNameAction_mem_hierarchy {P N f τ γ : V}
    (hγ : IsChoicelessInaccessible γ) (hP : P ∈ hierarchy γ)
    (hN : N ⊆ P) (hf : f ∈ N ^ P) (hτ : IsForcingName P τ) (hτγ : τ ∈ hierarchy γ) :
    nameAction f τ ∈ hierarchy γ := by
  let := hγ.1
  exact nameAction_mem_hierarchy_of_inaccessible hγ hP
    (suborderMap_mem_hierarchy hγ.rankCriterion.2.2.1 hP hN hf) hτγ hτ

variable {P R one δ Q S γ : V} [IsOrdinal δ]

local notation "Cₛ" => boundedNameTwoStep P R δ Q
local notation "Cₙ" => normalizedNameTwoStep P R one δ Q

/-- The earlier full carrier bounds the specified comparison map at the next
inaccessible cutoff. -/
theorem guardedTwoStepMap_mem_hierarchy
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hγ : IsChoicelessInaccessible γ) (hC : Cₛ ∈ hierarchy γ) :
    guardedTwoStepMap P R one δ Q ∈ hierarchy γ := by
  let := hγ.1
  exact suborderMap_mem_hierarchy hγ.rankCriterion.2.2.1 hC
    (normalizedNameTwoStep_subset hR ht) (guardedTwoStepMap_function hR ht hδ hP h0)

theorem normalizedTwoStepRetraction_mem_hierarchy
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hγ : IsChoicelessInaccessible γ) (hC : Cₛ ∈ hierarchy γ) :
    normalizedTwoStepRetraction P R one δ Q ∈ hierarchy γ := by
  let := hγ.1
  exact suborderMap_mem_hierarchy hγ.rankCriterion.2.2.1 hC
    (normalizedNameTwoStep_subset hR ht) (normalizedTwoStepRetraction_spec hR ht hδ hP hI).maps

theorem guardedTwoStepMap_nameAction_mem_hierarchy {τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hγ : IsChoicelessInaccessible γ) (hC : Cₛ ∈ hierarchy γ)
    (hτ : IsForcingName Cₛ τ) (hτγ : τ ∈ hierarchy γ) :
    IsForcingName Cₙ (nameAction (guardedTwoStepMap P R one δ Q) τ) ∧
      nameAction (guardedTwoStepMap P R one δ Q) τ ∈ hierarchy γ := by
  have hf := guardedTwoStepMap_function hR ht hδ hP h0
  exact ⟨nameAction_isName hf hτ,
    suborderNameAction_mem_hierarchy hγ hC (normalizedNameTwoStep_subset hR ht) hf hτ hτγ⟩

theorem normalizedTwoStepRetraction_nameAction_mem_hierarchy {τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hγ : IsChoicelessInaccessible γ) (hC : Cₛ ∈ hierarchy γ)
    (hτ : IsForcingName Cₛ τ) (hτγ : τ ∈ hierarchy γ) :
    IsForcingName Cₙ (nameAction (normalizedTwoStepRetraction P R one δ Q) τ) ∧
      nameAction (normalizedTwoStepRetraction P R one δ Q) τ ∈ hierarchy γ := by
  have hf := (normalizedTwoStepRetraction_spec hR ht hδ hP hI).maps
  exact ⟨nameAction_isName hf hτ,
    suborderNameAction_mem_hierarchy hγ hC (normalizedNameTwoStep_subset hR ht) hf hτ hτγ⟩

theorem normalizedTwoStepRetraction_nameAction_fixes {τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hτ : IsForcingName Cₙ τ) : nameAction (normalizedTwoStepRetraction P R one δ Q) τ = τ :=
  nameAction_eq_self_of_fixes_conditions (normalizedTwoStepRetraction_spec hR ht hδ hP hI).fixes hτ

theorem boundedNameTwoStep_mem_larger_hierarchy [IsOrdinal γ]
    (hγ : ∀ β ∈ γ, succ β ∈ γ) (hδγ : δ ∈ γ) (hP : P ∈ hierarchy δ) :
    Cₛ ∈ hierarchy γ := by
  have hV : hierarchy δ ∈ hierarchy γ := by
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hδγ
  exact subset_mem_hierarchy_limit hγ
    (prod_mem_hierarchy_limit hγ (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδγ) P hP) hV) sep_subset

/-- All data and both name translations used in the comparison stay below the
next inaccessible cutoff. The carrier bound is derived from the earlier height. -/
theorem normalizedTwoStep_comparison_rank_bounds
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hγ : IsChoicelessInaccessible γ) (hδγ : δ ∈ γ) :
    Cₛ ∈ hierarchy γ ∧ Cₙ ∈ hierarchy γ ∧
    guardedTwoStepMap P R one δ Q ∈ hierarchy γ ∧
    normalizedTwoStepRetraction P R one δ Q ∈ hierarchy γ ∧
    ∀ τ, IsForcingName Cₛ τ → τ ∈ hierarchy γ →
      (IsForcingName Cₙ (nameAction (guardedTwoStepMap P R one δ Q) τ) ∧
        nameAction (guardedTwoStepMap P R one δ Q) τ ∈ hierarchy γ) ∧
      (IsForcingName Cₙ (nameAction (normalizedTwoStepRetraction P R one δ Q) τ) ∧
        nameAction (normalizedTwoStepRetraction P R one δ Q) τ ∈ hierarchy γ) := by
  let := hγ.1
  have hC := boundedNameTwoStep_mem_larger_hierarchy (Q := Q) (R := R) hγ.rankCriterion.2.2.1 hδγ hP
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  exact ⟨hC, subset_mem_hierarchy_limit hγ.rankCriterion.2.2.1 hC (normalizedNameTwoStep_subset hR ht),
    guardedTwoStepMap_mem_hierarchy hR ht hδ hP h0 hγ hC,
    normalizedTwoStepRetraction_mem_hierarchy hR ht hδ hP hI hγ hC,
    fun _ hτ hτγ ↦ ⟨guardedTwoStepMap_nameAction_mem_hierarchy hR ht hδ hP h0 hγ hC hτ hτγ,
      normalizedTwoStepRetraction_nameAction_mem_hierarchy hR ht hδ hP hI hγ hC hτ hτγ⟩⟩

end ZFVP
