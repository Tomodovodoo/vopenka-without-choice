import ZFVP.SetTheory.ChoicelessFailureClub
import ZFVP.SetTheory.FormulaReflection

/-! Failure ranks with additional correctness, and their isolated successors.
Additional correctness permits transport of C(n) by the rank embeddings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsChoicelessFailureStage (n k : ℕ) (α β : V) : Prop :=
  IsChoicelessFailureLimit n α β ∧ Cn k β

instance isChoicelessFailureStage_definable (n k : ℕ) :
    ℒₛₑₜ-relation[V] (IsChoicelessFailureStage n k) := by
  unfold IsChoicelessFailureStage
  definability

theorem choicelessFailureStage_unbounded (n k : ℕ) (α ξ : V)
    [IsOrdinal α] [IsOrdinal ξ]
    (h : ∀ γ, ¬IsAlphaChoicelessExtendible n α γ) :
    ∃ β, ξ ∈ β ∧ IsChoicelessFailureStage n k α β := by
  let := ordinal_union_ordinal α ξ
  let := ordinal_union_ordinal (α ∪ ξ) (ω : V)
  let R := ChoicelessFailureWitness n α
  let S := fun x y : V ↦ x ∈ y ∧ Cn k y
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hS : ℒₛₑₜ-relation S := by unfold S; definability
  obtain ⟨β, hβ, hb, hlim, hw⟩ := witnessClosed_above
    (mergeWitnessRelations R S) (mergeWitnessRelations_definable R S hR hS)
    ((α ∪ ξ) ∪ (ω : V))
  let := hβ
  have hαξ : α ∪ ξ ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hb
  have hω : (ω : V) ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hb
  have haβ : α ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hαξ
  have hξβ : ξ ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hαξ
  obtain ⟨hr, hs⟩ := mergeWitnessClosed hω hlim hw
  refine ⟨β, hξβ, ⟨hβ, haβ, hlim, ?_⟩, ?_⟩
  · intro γ hγ hαγ
    let : IsOrdinal γ := IsOrdinal.of_mem hγ
    obtain ⟨μ, hμ, hwμ⟩ := hr γ (ordinal_subset_hierarchy β γ hγ)
      (choicelessFailureWitness_exists hαγ (h γ))
    let := hwμ.1.ordinal
    have hμβ : μ ∈ β := by
      simpa only [rank_of_ordinal] using (mem_hierarchy_iff_rank_mem μ β).mp hμ
    exact ⟨μ, hμβ, hwμ⟩
  · apply cn_closed k ⟨α, haβ⟩
    intro γ hγ
    let : IsOrdinal γ := IsOrdinal.of_mem hγ
    obtain ⟨μ, hμ, hγμ, hc⟩ := hs γ (ordinal_subset_hierarchy β γ hγ) (cn_unbounded k γ)
    let := hc.ordinal
    have hμβ : μ ∈ β := by
      simpa only [rank_of_ordinal] using (mem_hierarchy_iff_rank_mem μ β).mp hμ
    exact ⟨μ, hμβ, hγμ, hc⟩

theorem choicelessFailureStage_closed {n k : ℕ} {α β : V} [IsOrdinal β]
    (hβ : IsNonempty β)
    (hc : ∀ ξ ∈ β, ∃ δ ∈ β, ξ ∈ δ ∧ IsChoicelessFailureStage n k α δ) :
    IsChoicelessFailureStage n k α β := by
  constructor
  · apply choicelessFailureLimit_closed hβ
    intro ξ hξ
    obtain ⟨δ, hδ, hξδ, hD, _⟩ := hc ξ hξ
    exact ⟨δ, hδ, hξδ, hD⟩
  · apply cn_closed k hβ
    intro ξ hξ
    obtain ⟨δ, hδ, hξδ, _, hC⟩ := hc ξ hξ
    exact ⟨δ, hδ, hξδ, hC⟩

def IsNextChoicelessFailureStage (n k : ℕ) (α σ β : V) : Prop :=
  IsLeastOrdinal (fun δ ↦ σ ∈ δ ∧ IsChoicelessFailureStage n k α δ) β

instance isNextChoicelessFailureStage_definable (n k : ℕ) :
    ℒₛₑₜ-relation₃[V] (IsNextChoicelessFailureStage n k) := by
  unfold IsNextChoicelessFailureStage IsLeastOrdinal
  definability

theorem nextChoicelessFailureStage_existsUnique (n k : ℕ) (α σ : V)
    [IsOrdinal α] [IsOrdinal σ]
    (h : ∀ γ, ¬IsAlphaChoicelessExtendible n α γ) :
    ∃! β, IsNextChoicelessFailureStage n k α σ β := by
  apply leastOrdinal_existsUnique _ (by definability)
  obtain ⟨β, hσβ, hβ⟩ := choicelessFailureStage_unbounded n k α σ h
  exact ⟨β, hβ.1.1, hσβ, hβ⟩

theorem IsNextChoicelessFailureStage.no_between {n k : ℕ} {α σ β δ : V}
    (h : IsNextChoicelessFailureStage n k α σ β)
    (hδ : IsChoicelessFailureStage n k α δ) (hσδ : σ ∈ δ) : β ⊆ δ :=
  h.2.2 δ hδ.1.1 ⟨hσδ, hδ⟩

theorem IsNextChoicelessFailureStage.unique {n k : ℕ} {α σ β δ : V}
    (hβ : IsNextChoicelessFailureStage n k α σ β)
    (hδ : IsNextChoicelessFailureStage n k α σ δ) : β = δ :=
  subset_antisymm (hβ.no_between hδ.2.1.2 hδ.2.1.1)
    (hδ.no_between hβ.2.1.2 hβ.2.1.1)

end ZFVP
