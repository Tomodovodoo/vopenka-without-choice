import ZFVP.SetTheory.ClubSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsStationaryIn (S κ : V) : Prop := S ⊆ κ ∧ ∀ C, IsClubIn C κ → ∃ δ ∈ S, δ ∈ C

instance isStationaryIn_definable : ℒₛₑₜ-relation[V] IsStationaryIn := by
  unfold IsStationaryIn
  definability

theorem stationary_mono {S T κ : V} (hS : IsStationaryIn S κ) (hST : S ⊆ T) (hT : T ⊆ κ) :
    IsStationaryIn T κ := by
  refine ⟨hT, ?_⟩
  intro C hC
  obtain ⟨δ, hδ, hδC⟩ := hS.2 C hC
  exact ⟨δ, hST δ hδ, hδC⟩

theorem club_isStationary {C κ : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hC : IsClubIn C κ) : IsStationaryIn C κ := by
  refine ⟨hC.1.1, ?_⟩
  intro D hD
  obtain ⟨δ, hδ, _⟩ := (club_inter hκ hω hC hD).2.2 0 (hκ.2.1 _ (by simp))
  exact ⟨δ, (mem_inter_iff.mp hδ).1, (mem_inter_iff.mp hδ).2⟩

theorem stationary_inter_club {S C κ : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hS : IsStationaryIn S κ) (hC : IsClubIn C κ) : IsStationaryIn (S ∩ C) κ := by
  refine ⟨fun x hx ↦ hS.1 x (mem_inter_iff.mp hx).1, ?_⟩
  intro D hD
  obtain ⟨δ, hδS, hδ⟩ := hS.2 (C ∩ D) (club_inter hκ hω hC hD)
  exact ⟨δ, mem_inter_iff.mpr ⟨hδS, (mem_inter_iff.mp hδ).1⟩, (mem_inter_iff.mp hδ).2⟩

noncomputable def ordinalTail (κ β : V) : V := {η ∈ κ ; β ∈ η}

theorem ordinalTail_club {κ β : V} (hκ : IsRegularCardinal κ) (hβ : β ∈ κ) :
    IsClubIn (ordinalTail κ β) κ := by
  have : IsOrdinal κ := hκ.1.1
  have hsub : ordinalTail κ β ⊆ κ := fun _ h ↦ (mem_sep_iff.mp h).1
  refine ⟨⟨hsub, ?_⟩, ⟨hsub, ?_⟩⟩
  · intro δ hδ hn hcof
    have : IsOrdinal δ := IsOrdinal.of_mem hδ
    have hzero : (0 : V) ∈ δ := by
      rcases IsOrdinal.subset_iff.mp (show (0 : V) ⊆ δ from fun _ h ↦ False.elim (not_mem_empty h)) with heq | hlt
      · exact False.elim (hn heq.symm)
      · exact hlt
    obtain ⟨η, hη, hηδ, _⟩ := hcof 0 hzero
    exact mem_sep_iff.mpr ⟨hδ,
      IsOrdinal.toIsTransitive.transitive η hηδ β (mem_sep_iff.mp hη).2⟩
  · intro ξ hξ
    have hmax := ordinal_union_mem hξ hβ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    have : IsOrdinal (ξ ∪ β) := IsOrdinal.of_mem hmax
    have hs := regularCardinal_succ_closed hκ hmax
    have hξs : ξ ∈ succ (ξ ∪ β) := mem_succ_iff.mpr
      (IsOrdinal.subset_iff.mp (subset_union_left ξ β))
    have hβs : β ∈ succ (ξ ∪ β) := mem_succ_iff.mpr
      (IsOrdinal.subset_iff.mp (subset_union_right ξ β))
    exact ⟨succ (ξ ∪ β), mem_sep_iff.mpr ⟨hs, hβs⟩, hξs⟩

theorem stationary_unbounded {S κ : V} (hκ : IsRegularCardinal κ) (hS : IsStationaryIn S κ) :
    IsUnboundedIn S κ := by
  refine ⟨hS.1, ?_⟩
  intro ξ hξ
  obtain ⟨η, hη, htail⟩ := hS.2 (ordinalTail κ ξ) (ordinalTail_club hκ hξ)
  exact ⟨η, hη, (mem_sep_iff.mp htail).2⟩

theorem nonstationary_union {S T κ : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hS : S ⊆ κ) (hT : T ⊆ κ) (hnS : ¬IsStationaryIn S κ) (hnT : ¬IsStationaryIn T κ) :
    ¬IsStationaryIn (S ∪ T) κ := by
  classical
  have hCS : ¬∀ C, IsClubIn C κ → ∃ δ ∈ S, δ ∈ C := fun h ↦ hnS ⟨hS, h⟩
  have hCT : ¬∀ C, IsClubIn C κ → ∃ δ ∈ T, δ ∈ C := fun h ↦ hnT ⟨hT, h⟩
  push Not at hCS hCT
  obtain ⟨C, hC, hSC⟩ := hCS
  obtain ⟨D, hD, hTD⟩ := hCT
  intro hST
  obtain ⟨δ, hδ, hδCD⟩ := hST.2 (C ∩ D) (club_inter hκ hω hC hD)
  rcases mem_union_iff.mp hδ with hδ | hδ
  · exact hSC δ hδ (mem_inter_iff.mp hδCD).1
  · exact hTD δ hδ (mem_inter_iff.mp hδCD).2

end ZFVP
