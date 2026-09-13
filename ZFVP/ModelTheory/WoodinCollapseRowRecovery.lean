import ZFVP.ModelTheory.WoodinCollapseRankWitness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseRowWitness (r : V) : V := {⟨⟨r, (1 : V)⟩ₖ, (∅ : V)⟩ₖ}

theorem woodinCollapseRowWitness_mem {κ δ r : V} [IsOrdinal δ]
    (hκ : (1 : V) ∈ κ) (hδ : (1 : V) ∈ δ) (hr : r ∈ κ) :
    woodinCollapseRowWitness r ∈ woodinCollapse κ δ := by
  have : IsOrdinal (1 : V) := IsOrdinal.of_mem hδ
  have hzero : (∅ : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans
    (show (∅ : V) ∈ (1 : V) by change (∅ : V) ∈ succ ∅; simp) hδ
  apply (mem_woodinCollapse _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have he : z = ⟨⟨r, (1 : V)⟩ₖ, (∅ : V)⟩ₖ := mem_singleton_iff.mp hz
    rw [he]
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hr, hδ⟩, ordinal_subset_hierarchy δ ∅ hzero⟩
  · simp [woodinCollapseRowWitness]
  · refine ⟨1, hκ, ?_⟩
    have hd : domain (woodinCollapseRowWitness r) = {⟨r, (1 : V)⟩ₖ} := by
      ext a
      simp [woodinCollapseRowWitness, mem_domain_iff, kpair_iff]
    rw [hd]
    let d : ℒₛₑₜ-function₁[V] (fun _ : V ↦ (∅ : V)) := by definability
    refine ⟨definableGraph {⟨r, (1 : V)⟩ₖ} (fun _ ↦ ∅) d,
      definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by change (∅ : V) ∈ succ ∅; simp), ?_⟩
    intro a b z ha hb
    have haD := ((pair_mem_definableGraph_iff _ _ d _ _).mp ha).1
    have hbD := ((pair_mem_definableGraph_iff _ _ d _ _).mp hb).1
    exact (mem_singleton_iff.mp haD).trans (mem_singleton_iff.mp hbD).symm
  · intro α η x hx
    have he := kpair_iff.mp (mem_singleton_iff.mp hx)
    rw [he.2, (kpair_iff.mp he.1).2]
    apply ordinal_subset_hierarchy _
    exact ordinal_subset_add_right 1 (1 : V) ∅ (by change (∅ : V) ∈ succ ∅; simp)

theorem woodinCollapse_row_iff {κ δ r : V} [IsOrdinal δ]
    (hκ : (1 : V) ∈ κ) (hδ : (1 : V) ∈ δ) :
    r ∈ κ ↔ ∃ q ∈ woodinCollapse κ δ, ∃ ξ, ⟨r, ξ⟩ₖ ∈ domain q := by
  constructor
  · intro hr
    refine ⟨woodinCollapseRowWitness r, woodinCollapseRowWitness_mem hκ hδ hr, 1, ?_⟩
    exact mem_domain_of_kpair_mem (mem_singleton_iff.mpr rfl)
  · rintro ⟨q, hq, ξ, hξ⟩
    obtain ⟨x, hx⟩ := mem_domain_iff.mp hξ
    have hm := ((mem_woodinCollapse _ _ _).mp hq).1 _ hx
    exact (kpair_mem_iff.mp (kpair_mem_iff.mp hm).1).1

noncomputable def collapseRowIndices (C : V) : V := domain (⋃ˢ repl domain (by definability) C)

instance collapseRowIndices_definable : ℒₛₑₜ-function₁[V] collapseRowIndices := by
  unfold collapseRowIndices
  definability

theorem mem_collapseRowIndices_iff {C r : V} :
    r ∈ collapseRowIndices C ↔ ∃ q ∈ C, ∃ ξ, ⟨r, ξ⟩ₖ ∈ domain q := by
  unfold collapseRowIndices
  rw [mem_domain_iff]
  constructor
  · rintro ⟨ξ, hξ⟩
    obtain ⟨D, hD, hξ⟩ := mem_sUnion_iff.mp hξ
    obtain ⟨q, hq, rfl⟩ := (repl_spec (by definability)).mp hD
    exact ⟨q, hq, ξ, hξ⟩
  · rintro ⟨q, hq, ξ, hξ⟩
    exact ⟨ξ, mem_sUnion_iff.mpr ⟨domain q, (repl_spec (by definability)).mpr ⟨q, hq, rfl⟩, hξ⟩⟩

theorem collapseRowIndices_woodinCollapse {κ δ : V} [IsOrdinal δ]
    (hκ : (1 : V) ∈ κ) (hδ : (1 : V) ∈ δ) :
    collapseRowIndices (woodinCollapse κ δ) = κ := by
  apply mem_ext
  intro r
  rw [mem_collapseRowIndices_iff]
  exact (woodinCollapse_row_iff hκ hδ).symm

end ZFVP
