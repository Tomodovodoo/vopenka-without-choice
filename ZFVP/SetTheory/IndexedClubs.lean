import ZFVP.SetTheory.ClubDictionary
import ZFVP.SetTheory.IterationLimit

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def indexedClubIntersection (κ μ C : V) : V := {δ ∈ κ ; ∀ i ∈ μ, δ ∈ C ‘ i}

noncomputable def clubNextValue (C i x : V) : V := nextIn (C ‘ i) x

instance clubNextValue_definable : ℒₛₑₜ-function₃[V] clubNextValue := by
  unfold clubNextValue
  exact Language.DefinableFunction₂.comp (by definability) (by definability)

noncomputable def clubNextRange (C μ x : V) : V :=
  repl (fun i ↦ nextIn (C ‘ i) x)
    (Language.DefinableFunction₂.comp (by definability) (by definability)) μ

instance clubNextRange_definable : ℒₛₑₜ-function₃[V] clubNextRange := by
  have h : ℒₛₑₜ-relation₄[V] (fun R C μ x ↦ ∀ y, y ∈ R ↔ ∃ i ∈ μ, y = clubNextValue C i x) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional (by definability)
    apply Language.Definable.exs
    apply Language.Definable.and (by definability)
    exact Language.DefinableRel.comp (by definability)
      (Language.DefinableFunction₃.comp (by definability) (by definability) (by definability))
  apply Language.Definable.of_iff h
  intro v
  change v 0 = clubNextRange (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [clubNextValue, clubNextRange, repl_spec]

theorem mem_clubNextRange (C μ x y : V) : y ∈ clubNextRange C μ x ↔ ∃ i ∈ μ, y = nextIn (C ‘ i) x :=
  repl_spec (show ℒₛₑₜ-function₁ (fun i ↦ nextIn (C ‘ i) x) from
    Language.DefinableFunction₂.comp (by definability) (by definability))

theorem clubNextRange_bounded {κ μ C x : V} (hκ : IsRegularCardinal κ) (hμ : μ ∈ κ)
    (hC : ∀ i ∈ μ, IsClubIn (C ‘ i) κ) (hx : x ∈ κ) : ⋃ˢ clubNextRange C μ x ∈ κ := by
  have : IsOrdinal κ := hκ.1.1
  let f := definableGraph μ (fun i ↦ nextIn (C ‘ i) x)
    (Language.DefinableFunction₂.comp (by definability) (by definability))
  have hf : f ∈ κ ^ μ := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i hi ↦ (hC i hi).2.1 _ (nextIn_spec (hC i hi).2 hx).1)
  have heq : range f = clubNextRange C μ x := range_definableGraph _ _ _
  rw [← heq]
  exact union_range_below_cofinality (hκ.2.2.symm ▸ hμ) hf

theorem indexedClubIntersection_club {κ μ C : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hμ : μ ∈ κ) (hC : ∀ i ∈ μ, IsClubIn (C ‘ i) κ) :
    IsClubIn (indexedClubIntersection κ μ C) κ := by
  have : IsOrdinal κ := hκ.1.1
  have hsub : indexedClubIntersection κ μ C ⊆ κ := fun _ h ↦ (mem_sep_iff.mp h).1
  refine ⟨⟨hsub, ?_⟩, ⟨hsub, ?_⟩⟩
  · intro δ hδ hn hcof
    apply mem_sep_iff.mpr
    refine ⟨hδ, ?_⟩
    intro i hi
    apply (hC i hi).1.2 δ hδ hn
    intro x hx
    obtain ⟨η, hη, hηδ, hxη⟩ := hcof x hx
    exact ⟨η, (mem_sep_iff.mp hη).2 i hi, hηδ, hxη⟩
  · intro ξ hξ
    let F : V → V := fun x ↦ succ (x ∪ ⋃ˢ clubNextRange C μ x)
    have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
    have hstep (x : V) (hx : x ∈ κ) : F x ∈ κ ∧ x ∈ F x := by
      have hr := clubNextRange_bounded hκ hμ hC hx
      have hm := ordinal_union_mem hx hr
      have : IsOrdinal x := IsOrdinal.of_mem hx
      have : IsOrdinal (x ∪ ⋃ˢ clubNextRange C μ x) := IsOrdinal.of_mem hm
      exact ⟨regularCardinal_succ_closed hκ hm,
        mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_left _ _))⟩
    have hnext (x : V) (hx : x ∈ κ) (i : V) (hi : i ∈ μ) : nextIn (C ‘ i) x ∈ F x := by
      have hr := clubNextRange_bounded hκ hμ hC hx
      have hm := ordinal_union_mem hx hr
      have hn := nextIn_spec (hC i hi).2 hx
      have : IsOrdinal (nextIn (C ‘ i) x) := IsOrdinal.of_mem ((hC i hi).2.1 _ hn.1)
      have : IsOrdinal (x ∪ ⋃ˢ clubNextRange C μ x) := IsOrdinal.of_mem hm
      have hmem : nextIn (C ‘ i) x ∈ clubNextRange C μ x :=
        (mem_clubNextRange C μ x _).mpr ⟨i, hi, rfl⟩
      exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
        (subset_trans (subset_sUnion_of_mem hmem) (subset_union_right _ _)))
    obtain ⟨δ, hδ, hξδ, haδ, hcof⟩ := increasingIteration_limit (hκ.2.2.symm ▸ hω) F hF hξ hstep
    have : IsOrdinal δ := IsOrdinal.of_mem hδ
    have hn : δ ≠ 0 := fun heq ↦ not_mem_empty (heq ▸ hξδ)
    refine ⟨δ, mem_sep_iff.mpr ⟨hδ, ?_⟩, hξδ⟩
    intro i hi
    apply (hC i hi).1.2 δ hδ hn
    intro x hx
    obtain ⟨n, hnω, hxan⟩ := hcof x hx
    let a := naturalIteration F hF ξ
    have hanκ : a n ∈ κ := IsOrdinal.toIsTransitive.transitive δ hδ _ (haδ n hnω)
    have hci := nextIn_spec (hC i hi).2 hanκ
    have hciδ : nextIn (C ‘ i) (a n) ∈ δ := by
      apply IsOrdinal.toIsTransitive.transitive (a (succ n)) (haδ _ (ω_succ_closed hnω))
      change nextIn (C ‘ i) (a n) ∈ naturalIteration F hF ξ (succ n)
      rw [naturalIteration_succ F hF ξ hnω]
      exact hnext _ hanκ i hi
    have : IsOrdinal (nextIn (C ‘ i) (a n)) := IsOrdinal.of_mem ((hC i hi).2.1 _ hci.1)
    exact ⟨nextIn (C ‘ i) (a n), hci.1, hciδ,
      IsOrdinal.toIsTransitive.transitive _ hci.2 x hxan⟩

end ZFVP
