import ZFVP.SetTheory.IndexedClubs

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def diagonalClubIntersection (κ C : V) : V := {δ ∈ κ ; ∀ i ∈ δ, δ ∈ C ‘ i}

theorem diagonalClubIntersection_club {κ C : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hC : ∀ i ∈ κ, IsClubIn (C ‘ i) κ) :
    IsClubIn (diagonalClubIntersection κ C) κ := by
  have : IsOrdinal κ := hκ.1.1
  have hsub : diagonalClubIntersection κ C ⊆ κ := fun _ h ↦ (mem_sep_iff.mp h).1
  refine ⟨⟨hsub, ?_⟩, ⟨hsub, ?_⟩⟩
  · intro δ hδ hn hcof
    have : IsOrdinal δ := IsOrdinal.of_mem hδ
    apply mem_sep_iff.mpr
    refine ⟨hδ, ?_⟩
    intro i hi
    have hiκ := IsOrdinal.toIsTransitive.transitive δ hδ i hi
    apply (hC i hiκ).1.2 δ hδ hn
    intro x hx
    obtain ⟨η, hη, hηδ, hmaxη⟩ := hcof (x ∪ i) (ordinal_union_mem hx hi)
    have : IsOrdinal η := IsOrdinal.of_mem hηδ
    have hsubη := IsOrdinal.toIsTransitive.transitive (x ∪ i) hmaxη
    have hiη : i ∈ η := by
      have : IsOrdinal i := IsOrdinal.of_mem hi
      have : IsOrdinal (x ∪ i) := IsOrdinal.of_mem (ordinal_union_mem hx hi)
      rcases IsOrdinal.subset_iff.mp (subset_union_right x i) with heq | hlt
      · exact heq ▸ hmaxη
      · exact hsubη i hlt
    have hxη : x ∈ η := by
      have : IsOrdinal x := IsOrdinal.of_mem hx
      have : IsOrdinal (x ∪ i) := IsOrdinal.of_mem (ordinal_union_mem hx hi)
      rcases IsOrdinal.subset_iff.mp (subset_union_left x i) with heq | hlt
      · exact heq ▸ hmaxη
      · exact hsubη x hlt
    exact ⟨η, (mem_sep_iff.mp hη).2 i hiη, hηδ, hxη⟩
  · intro ξ hξ
    let F : V → V := fun x ↦ succ (x ∪ ⋃ˢ clubNextRange C x x)
    have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
    have hprefix (x : V) (hx : x ∈ κ) : ∀ i ∈ x, IsClubIn (C ‘ i) κ :=
      fun i hi ↦ hC i (IsOrdinal.toIsTransitive.transitive x hx i hi)
    have hstep (x : V) (hx : x ∈ κ) : F x ∈ κ ∧ x ∈ F x := by
      have hr := clubNextRange_bounded hκ hx (hprefix x hx) hx
      have hm := ordinal_union_mem hx hr
      have : IsOrdinal x := IsOrdinal.of_mem hx
      have : IsOrdinal (x ∪ ⋃ˢ clubNextRange C x x) := IsOrdinal.of_mem hm
      exact ⟨regularCardinal_succ_closed hκ hm,
        mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_left _ _))⟩
    have hnext (x : V) (hx : x ∈ κ) (i : V) (hi : i ∈ x) : nextIn (C ‘ i) x ∈ F x := by
      have hr := clubNextRange_bounded hκ hx (hprefix x hx) hx
      have hm := ordinal_union_mem hx hr
      have hn := nextIn_spec (hprefix x hx i hi).2 hx
      have : IsOrdinal (nextIn (C ‘ i) x) := IsOrdinal.of_mem ((hprefix x hx i hi).2.1 _ hn.1)
      have : IsOrdinal (x ∪ ⋃ˢ clubNextRange C x x) := IsOrdinal.of_mem hm
      have hmem : nextIn (C ‘ i) x ∈ clubNextRange C x x :=
        (mem_clubNextRange C x x _).mpr ⟨i, hi, rfl⟩
      exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
        (subset_trans (subset_sUnion_of_mem hmem) (subset_union_right _ _)))
    obtain ⟨δ, hδ, hξδ, haδ, hcof⟩ := increasingIteration_limit (hκ.2.2.symm ▸ hω) F hF hξ hstep
    have : IsOrdinal δ := IsOrdinal.of_mem hδ
    have hn : δ ≠ 0 := fun heq ↦ not_mem_empty (heq ▸ hξδ)
    refine ⟨δ, mem_sep_iff.mpr ⟨hδ, ?_⟩, hξδ⟩
    intro i hi
    have hiκ := IsOrdinal.toIsTransitive.transitive δ hδ i hi
    apply (hC i hiκ).1.2 δ hδ hn
    intro x hx
    obtain ⟨n, hnω, hmaxan⟩ := hcof (x ∪ i) (ordinal_union_mem hx hi)
    let a := naturalIteration F hF ξ
    have hanκ : a n ∈ κ := IsOrdinal.toIsTransitive.transitive δ hδ _ (haδ n hnω)
    have : IsOrdinal (a n) := IsOrdinal.of_mem hanκ
    have : IsOrdinal x := IsOrdinal.of_mem hx
    have : IsOrdinal i := IsOrdinal.of_mem hi
    have : IsOrdinal (x ∪ i) := IsOrdinal.of_mem (ordinal_union_mem hx hi)
    have hian : i ∈ a n := by
      rcases IsOrdinal.subset_iff.mp (subset_union_right x i) with heq | hlt
      · exact heq ▸ hmaxan
      · exact IsOrdinal.toIsTransitive.transitive (x ∪ i) hmaxan i hlt
    have hxan : x ∈ a n := by
      rcases IsOrdinal.subset_iff.mp (subset_union_left x i) with heq | hlt
      · exact heq ▸ hmaxan
      · exact IsOrdinal.toIsTransitive.transitive (x ∪ i) hmaxan x hlt
    have hci := nextIn_spec (hC i hiκ).2 hanκ
    have hciδ : nextIn (C ‘ i) (a n) ∈ δ := by
      apply IsOrdinal.toIsTransitive.transitive (a (succ n)) (haδ _ (ω_succ_closed hnω))
      change nextIn (C ‘ i) (a n) ∈ naturalIteration F hF ξ (succ n)
      rw [naturalIteration_succ F hF ξ hnω]
      exact hnext _ hanκ i hian
    have : IsOrdinal (nextIn (C ‘ i) (a n)) := IsOrdinal.of_mem ((hC i hiκ).2.1 _ hci.1)
    exact ⟨nextIn (C ‘ i) (a n), hci.1, hciδ,
      IsOrdinal.toIsTransitive.transitive _ hci.2 x hxan⟩

theorem regressive_meets_club_family {κ S r C : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hS : IsStationaryIn S κ)
    (hr : ∀ δ ∈ S, r ‘ δ ∈ δ) (hC : ∀ i ∈ κ, IsClubIn (C ‘ i) κ) :
    ∃ δ ∈ S, δ ∈ C ‘ (r ‘ δ) := by
  obtain ⟨δ, hδS, hδ⟩ := hS.2 (diagonalClubIntersection κ C)
    (diagonalClubIntersection_club hκ hω hC)
  exact ⟨δ, hδS, (mem_sep_iff.mp hδ).2 _ (hr δ hδS)⟩

theorem no_club_family_avoiding_regressive_fibers {κ S r C : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hS : IsStationaryIn S κ)
    (hr : ∀ δ ∈ S, r ‘ δ ∈ δ) (hC : ∀ i ∈ κ, IsClubIn (C ‘ i) κ)
    (havoid : ∀ i ∈ κ, ∀ δ ∈ S, r ‘ δ = i → δ ∉ C ‘ i) : False := by
  have : IsOrdinal κ := hκ.1.1
  obtain ⟨δ, hδ, hδC⟩ := regressive_meets_club_family hκ hω hS hr hC
  have hrκ : r ‘ δ ∈ κ := IsOrdinal.toIsTransitive.transitive δ (hS.1 δ hδ) _ (hr δ hδ)
  exact havoid _ hrκ δ hδ rfl hδC

end ZFVP
