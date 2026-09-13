import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.OrdinalLeftOne
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.InternalWellFounded

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseRankWitness (β : V) : V :=
  {⟨⟨∅, succ (succ β)⟩ₖ, β⟩ₖ}

instance woodinCollapseRankWitness_definable : ℒₛₑₜ-function₁[V] woodinCollapseRankWitness := by
  unfold woodinCollapseRankWitness
  definability

theorem woodinCollapseRankWitness_mem_of_coordinate {κ δ β : V}
    [IsOrdinal κ] [IsOrdinal δ] [IsOrdinal β]
    (hκ : (1 : V) ∈ κ) (hη : succ (succ β) ∈ δ) :
    woodinCollapseRankWitness β ∈ woodinCollapse κ δ := by
  have : IsOrdinal (1 : V) := IsOrdinal.of_mem hκ
  have hβ : β ∈ δ := IsOrdinal.toIsTransitive.mem_trans
    (mem_succ_iff.mpr (Or.inr (mem_succ_self β))) hη
  have h0 : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans
    (show (∅ : V) ∈ 1 by change (∅ : V) ∈ succ ∅; simp) hκ
  have hβV : β ∈ hierarchy δ := ordinal_subset_hierarchy δ β hβ
  apply (mem_woodinCollapse _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z = ⟨⟨∅, succ (succ β)⟩ₖ, β⟩ₖ := by simpa [woodinCollapseRankWitness] using hz
    rw [hz']
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨h0, hη⟩, hβV⟩
  · simp [woodinCollapseRankWitness]
  · refine ⟨1, hκ, ?_⟩
    have hd : domain (woodinCollapseRankWitness β) = {⟨∅, succ (succ β)⟩ₖ} := by
      ext a
      simp [woodinCollapseRankWitness, mem_domain_iff, kpair_iff]
    rw [hd]
    let d : ℒₛₑₜ-function₁[V] (fun _ : V ↦ (∅ : V)) := by definability
    refine ⟨definableGraph {⟨∅, succ (succ β)⟩ₖ} (fun _ ↦ ∅) d,
      definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by change (∅ : V) ∈ succ ∅; simp), ?_⟩
    intro a b z ha hb
    have haD := ((pair_mem_definableGraph_iff _ _ d _ _).mp ha).1
    have hbD := ((pair_mem_definableGraph_iff _ _ d _ _).mp hb).1
    exact (mem_singleton_iff.mp haD).trans (mem_singleton_iff.mp hbD).symm
  · intro α η x hx
    have he : ⟨⟨α, η⟩ₖ, x⟩ₖ = ⟨⟨∅, succ (succ β)⟩ₖ, β⟩ₖ := by
      simpa [woodinCollapseRankWitness] using hx
    have hcoord := (kpair_iff.mp he).1
    rw [(kpair_iff.mp he).2, (kpair_iff.mp hcoord).2]
    apply ordinal_subset_hierarchy _
    exact ordinal_subset_add_right 1 (succ (succ β)) β
      (mem_succ_iff.mpr (Or.inr (mem_succ_self β)))

theorem woodinCollapseRankWitness_mem {κ δ β : V} [IsOrdinal κ] [IsOrdinal δ]
    (hκ : (1 : V) ∈ κ) (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (hβ : β ∈ δ) :
    woodinCollapseRankWitness β ∈ woodinCollapse κ δ := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  exact woodinCollapseRankWitness_mem_of_coordinate hκ (hδ _ (hδ _ hβ))

theorem woodinCollapseRankWitness_mem_hierarchy {δ β : V} [IsOrdinal δ]
    (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (hβ : β ∈ δ) :
    woodinCollapseRankWitness β ∈ hierarchy δ := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have hβV : β ∈ hierarchy δ := ordinal_subset_hierarchy δ β hβ
  have hη : succ (succ β) ∈ hierarchy δ := ordinal_subset_hierarchy δ _ (hδ _ (hδ _ hβ))
  have hz : (∅ : V) ∈ hierarchy δ := by
    apply ordinal_subset_hierarchy δ
    exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset β))) (hδ _ hβ)
  have hp := kpair_mem_hierarchy_limit hδ (kpair_mem_hierarchy_limit hδ hz hη) hβV
  simpa [woodinCollapseRankWitness] using pair_mem_hierarchy_limit hδ hp hp

theorem woodinCollapseRankWitness_nonempty (β : V) : woodinCollapseRankWitness β ≠ ∅ := by
  intro he
  have hm : ⟨⟨∅, succ (succ β)⟩ₖ, β⟩ₖ ∈ woodinCollapseRankWitness β := by
    simp [woodinCollapseRankWitness]
  rw [he] at hm
  exact not_mem_empty hm

theorem woodinCollapseRankWitness_rank (β : V) [IsOrdinal β] :
    β ∈ rank (woodinCollapseRankWitness β) := by
  have hh := IsOrdinal.toIsTransitive.mem_trans
    (rank_kpair_right_lt ⟨∅, succ (succ β)⟩ₖ β)
    (rank_mem (show ⟨⟨∅, succ (succ β)⟩ₖ, β⟩ₖ ∈ woodinCollapseRankWitness β by
      simp [woodinCollapseRankWitness]))
  simpa only [rank_of_ordinal] using hh

end ZFVP
