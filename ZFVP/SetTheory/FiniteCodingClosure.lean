import ZFVP.SetTheory.UniformCodingUniverse

/-! Every internally finite tuple of members of a coding universe belongs to it. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sUnion_mem_hierarchy_limit {κ X : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hX : X ∈ hierarchy κ) : ⋃ˢ X ∈ hierarchy κ := by
  have hr := (mem_hierarchy_iff_rank_mem X κ).mp hX
  apply mem_hierarchy_of_mem_stage (hκ _ hr)
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨y, hy, hz⟩ := mem_sUnion_iff.mp hz
  exact (hierarchy_transitive (rank X)).mem_trans hz (subset_hierarchy_rank X y hy)

theorem codingUniverse_sUnion_closed {X a : V} (ha : a ∈ codingUniverse X) :
    ⋃ˢ a ∈ codingUniverse X := sUnion_mem_hierarchy_limit (fun _ ↦ codingRank_succ_closed X) ha

theorem codingUniverse_union_closed {X a b : V}
    (ha : a ∈ codingUniverse X) (hb : b ∈ codingUniverse X) : a ∪ b ∈ codingUniverse X := by
  have h := codingUniverse_sUnion_closed (codingUniverse_pair_closed ha hb)
  simpa only [pair_eq_doubleton, ← union_def] using h

theorem codingUniverse_insert_closed {X a b : V}
    (ha : a ∈ codingUniverse X) (hb : b ∈ codingUniverse X) : insert a b ∈ codingUniverse X := by
  have hs : ({a} : V) ∈ codingUniverse X := by simpa using codingUniverse_pair_closed ha ha
  change ({a} : V) ∪ b ∈ codingUniverse X
  exact codingUniverse_union_closed hs hb

theorem codingUniverse_empty_mem (X : V) : (∅ : V) ∈ codingUniverse X :=
  (codingUniverse_transitive X).mem_trans empty_mem_ω (omega_mem_codingUniverse X)

theorem codingUniverse_natural_mem (X : V) {n : V} (hn : n ∈ (ω : V)) : n ∈ codingUniverse X :=
  (codingUniverse_transitive X).mem_trans hn (omega_mem_codingUniverse X)

theorem finiteSequence_mem_codingUniverse (X : V) {s : V}
    (hs : s ∈ finiteSequences (codingUniverse X)) : s ∈ codingUniverse X := by
  apply finiteSequence_induction (codingUniverse X) (fun s ↦ s ∈ codingUniverse X)
    (by definability) (codingUniverse_empty_mem X) ?_ s hs
  intro n hn t _ x hx ht
  exact codingUniverse_insert_closed
    (codingUniverse_kpair_closed (codingUniverse_natural_mem X hn) hx) ht

theorem kpair_components_mem_transitive {U x y : V} [hU : IsTransitive U]
    (hp : ⟨x, y⟩ₖ ∈ U) : x ∈ U ∧ y ∈ U := by
  have hs : ({x} : V) ∈ U := hU.mem_trans (by simp [kpair]) hp
  have hd : ({x, y} : V) ∈ U := hU.mem_trans (by simp [kpair]) hp
  exact ⟨hU.mem_trans (by simp) hs, hU.mem_trans (by simp) hd⟩

end ZFVP
