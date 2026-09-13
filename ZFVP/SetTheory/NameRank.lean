import ZFVP.SetTheory.NameClosureRecursion
import ZFVP.SetTheory.NameActionBounds
import ZFVP.SetTheory.SymmetricSystems
import ZFVP.SetTheory.TransfiniteIteration

/-! An ordinal rank on forcing names measured by the tree of subnames rather than by the
Kuratowski coding of conditions. The automorphism action rewrites conditions but not the
subname tree, so this rank is invariant under the action, and the names of rank below a
fixed ordinal form a set that the action preserves. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Small ordinal facts -/

theorem succ_subset_of_mem_ordinal {α β : V} [IsOrdinal α] (h : β ∈ α) : succ β ⊆ α := by
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hzb
  · exact h
  · exact IsOrdinal.toIsTransitive.mem_trans hzb h

theorem succ_subset_succ_of_subset {α β : V} [IsOrdinal α] [IsOrdinal β] (h : β ⊆ α) :
    succ β ⊆ succ α := by
  rcases IsOrdinal.subset_iff.mp h with rfl | h'
  · exact fun x hx ↦ hx
  · exact succ_subset_of_mem_ordinal (mem_succ_iff.mpr (Or.inr h'))

/-- The union of all ordinals belonging to `α`. For `α` an ordinal this is `⋃ˢ α`, but the
definition makes sense for any set and is always an ordinal. -/
noncomputable def ordinalSup (α : V) : V := ⋃ˢ {β ∈ α ; IsOrdinal β}

instance isOrdinal_ordinalSup (α : V) : IsOrdinal (ordinalSup α) :=
  IsOrdinal.sUnion (fun _ hβ ↦ (mem_sep_iff.mp hβ).2)

theorem subset_ordinalSup {α β : V} (hβ : IsOrdinal β) (h : β ∈ α) : β ⊆ ordinalSup α :=
  subset_sUnion_of_mem (mem_sep_iff.mpr ⟨h, hβ⟩)

/-! ### The rank of the subname tree -/

/-- The recursion step for `nameRank`: the union of the successors of the values already
computed on the subnames. -/
noncomputable def nameRankStep (τ g : V) : V :=
  ⋃ˢ repl (fun σ ↦ succ (g ‘ σ)) (by definability) (domain τ)

instance nameRankStep_definable : ℒₛₑₜ-function₂[V] nameRankStep := by
  have h : ℒₛₑₜ-relation₃ (fun C τ g : V ↦ ∀ z, z ∈ C ↔
      ∃ y, (∃ σ ∈ domain τ, y = succ (g ‘ σ)) ∧ z ∈ y) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameRankStep (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [nameRankStep, mem_sUnion_iff, repl_spec]

/-- The rank of a name in the tree of its subnames. -/
noncomputable def nameRank (τ : V) : V := subnameRecursion nameRankStep nameRankStep_definable τ

instance nameRank_definable : ℒₛₑₜ-function₁[V] nameRank :=
  subnameRecursion_definable nameRankStep nameRankStep_definable

theorem mem_nameRank_iff (τ z : V) :
    z ∈ nameRank τ ↔ ∃ σ ∈ domain τ, z ∈ succ (nameRank σ) := by
  rw [nameRank, subnameRecursion_equation]
  change z ∈ nameRankStep τ (definableGraph (domain τ) nameRank (by definability)) ↔ _
  simp only [nameRankStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨σ, hσ, rfl⟩ := hy
    exact ⟨σ, hσ, by rwa [value_definableGraph _ _ _ hσ] at hzy⟩
  · rintro ⟨σ, hσ, hz⟩
    exact ⟨_, ⟨σ, hσ, rfl⟩, by rwa [value_definableGraph _ _ _ hσ]⟩

/-- `nameRank τ` is the union over the subnames `σ` of `τ` of `succ (nameRank σ)`. -/
theorem nameRank_spec (τ : V) :
    nameRank τ = ⋃ˢ repl (fun σ ↦ succ (nameRank σ)) (by definability) (domain τ) := by
  apply mem_ext
  intro z
  rw [mem_nameRank_iff, mem_sUnion_iff]
  constructor
  · rintro ⟨σ, hσ, hz⟩
    exact ⟨_, (repl_spec (by definability)).mpr ⟨σ, hσ, rfl⟩, hz⟩
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨σ, hσ, rfl⟩ := (repl_spec (by definability)).mp hy
    exact ⟨σ, hσ, hzy⟩

theorem isOrdinal_nameRank (τ : V) : IsOrdinal (nameRank τ) := by
  have key : ∀ σ ∈ nameClosure τ, IsOrdinal (nameRank σ) := by
    apply projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
      (fun σ ↦ IsOrdinal (nameRank σ)) (by definability)
    intro σ hσ ih
    rw [nameRank_spec σ]
    apply IsOrdinal.sUnion
    intro y hy
    obtain ⟨ν, hν, rfl⟩ := (repl_spec (by definability)).mp hy
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hν
    have : IsOrdinal (nameRank ν) :=
      ih ν (nameClosure_closed τ σ hσ ν hν) (rank_subname_lt hp)
    exact inferInstance
  exact key τ (mem_nameClosure_self τ)

theorem nameRank_mem_of_mem_domain {σ τ : V} (h : σ ∈ domain τ) : nameRank σ ∈ nameRank τ :=
  (mem_nameRank_iff τ _).mpr ⟨σ, h, mem_succ_self _⟩

theorem nameRank_lt_of_subname {σ p τ : V} (h : ⟨σ, p⟩ₖ ∈ τ) : nameRank σ ∈ nameRank τ :=
  nameRank_mem_of_mem_domain (mem_domain_of_kpair_mem h)

theorem nameRank_le_of_forall {τ α : V} (hα : IsOrdinal α)
    (h : ∀ σ ∈ domain τ, nameRank σ ∈ α) : nameRank τ ⊆ α := by
  have : IsOrdinal α := hα
  intro z hz
  obtain ⟨σ, hσ, hzσ⟩ := (mem_nameRank_iff τ z).mp hz
  rcases mem_succ_iff.mp hzσ with rfl | hz'
  · exact h σ hσ
  · exact IsOrdinal.toIsTransitive.mem_trans hz' (h σ hσ)

/-! ### Invariance under the automorphism action -/

theorem mem_domain_nameAction_iff {P π τ : V} (hτ : IsForcingName P τ) (ν : V) :
    ν ∈ domain (nameAction π τ) ↔ ∃ σ ∈ domain τ, ν = nameAction π σ := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := mem_domain_iff.mp h
    obtain ⟨σ, p, hp, he⟩ := (mem_nameAction_iff hτ π _).mp hq
    exact ⟨σ, mem_domain_of_kpair_mem hp, (kpair_iff.mp he).1⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
    exact mem_domain_of_kpair_mem ((mem_nameAction_iff hτ π _).mpr ⟨σ, p, hp, rfl⟩)

/-- The action rewrites conditions but keeps the subname tree, so it keeps the name rank.
No hypothesis on `π` is needed beyond `τ` being a name. -/
theorem nameRank_nameAction_of_isName {P π τ : V} (hτ : IsForcingName P τ) :
    nameRank (nameAction π τ) = nameRank τ := by
  have key : ∀ σ ∈ nameClosure τ, nameRank (nameAction π σ) = nameRank σ := by
    apply projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
      (fun σ ↦ nameRank (nameAction π σ) = nameRank σ) (by definability)
    intro σ hσ ih
    have hσn : IsForcingName P σ := forcingName_mem_closure hτ hσ
    apply mem_ext
    intro z
    rw [mem_nameRank_iff, mem_nameRank_iff]
    constructor
    · rintro ⟨ν, hν, hz⟩
      obtain ⟨μ, hμ, rfl⟩ := (mem_domain_nameAction_iff hσn ν).mp hν
      obtain ⟨p, hp⟩ := mem_domain_iff.mp hμ
      exact ⟨μ, hμ, by rwa [ih μ (nameClosure_closed τ σ hσ μ hμ) (rank_subname_lt hp)] at hz⟩
    · rintro ⟨μ, hμ, hz⟩
      obtain ⟨p, hp⟩ := mem_domain_iff.mp hμ
      refine ⟨nameAction π μ, (mem_domain_nameAction_iff hσn _).mpr ⟨μ, hμ, rfl⟩, ?_⟩
      rwa [ih μ (nameClosure_closed τ σ hσ μ hμ) (rank_subname_lt hp)]
  exact key τ (mem_nameClosure_self τ)

theorem nameRank_nameAction {P R π τ : V} (_hπ : IsForcingAutomorphism P R π)
    (hτ : IsForcingName P τ) : nameRank (nameAction π τ) = nameRank τ :=
  nameRank_nameAction_of_isName hτ

/-! ### Stages of names -/

/-- One step of the stage hierarchy for names over `P`. -/
noncomputable def nameStageStep (P X : V) : V := X ∪ ℘ (X ×ˢ P)

instance nameStageStep_definable (P : V) : ℒₛₑₜ-function₁[V] (nameStageStep P) := by
  unfold nameStageStep
  definability

/-- The `α`-th stage of names over `P`: iterate `X ↦ X ∪ ℘ (X ×ˢ P)` from `∅`. -/
noncomputable def nameStage (P α : V) : V :=
  iterate (nameStageStep P) (nameStageStep_definable P) ∅ α

instance nameStage_definable (P : V) : ℒₛₑₜ-function₁[V] (nameStage P) :=
  iterate_definable (nameStageStep_definable P) ∅

theorem nameStageStep_inflationary (P X : V) : X ⊆ nameStageStep P X :=
  fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)

theorem nameStage_succ (P ξ : V) [IsOrdinal ξ] :
    nameStage P (succ ξ) = nameStageStep P (nameStage P ξ) :=
  iterate_succ (nameStageStep_definable P) ∅ ξ

theorem nameStage_mono {P β α : V} [IsOrdinal α] (h : β ∈ α) :
    nameStage P β ⊆ nameStage P α :=
  iterate_mono (nameStageStep_definable P) (nameStageStep_inflationary P) ∅
    (IsOrdinal.toOrdinal α) β h

theorem nameStage_mono_subset {P β α : V} (hβ : IsOrdinal β) (hα : IsOrdinal α) (h : β ⊆ α) :
    nameStage P β ⊆ nameStage P α := by
  have : IsOrdinal β := hβ
  have : IsOrdinal α := hα
  rcases IsOrdinal.subset_iff.mp h with rfl | h'
  · exact fun x hx ↦ hx
  · exact nameStage_mono h'

/-- A name lies in the stage one above its name rank. -/
theorem mem_nameStage_succ_nameRank {P τ : V} (hτ : IsForcingName P τ) :
    τ ∈ nameStage P (succ (nameRank τ)) := by
  have key : ∀ σ ∈ nameClosure τ, σ ∈ nameStage P (succ (nameRank σ)) := by
    apply projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
      (fun σ ↦ σ ∈ nameStage P (succ (nameRank σ))) (by definability)
    intro σ hσ ih
    have hσn : IsForcingName P σ := forcingName_mem_closure hτ hσ
    have hord : IsOrdinal (nameRank σ) := isOrdinal_nameRank σ
    have hsub : σ ⊆ nameStage P (nameRank σ) ×ˢ P := by
      intro z hz
      obtain ⟨ν, p, hp, rfl⟩ := hσn σ (mem_nameClosure_self σ) z hz
      have hνd : ν ∈ domain σ := mem_domain_of_kpair_mem (show ⟨ν, p⟩ₖ ∈ σ from hz)
      have hνc : ν ∈ nameClosure τ := nameClosure_closed τ σ hσ ν hνd
      have hν : ν ∈ nameStage P (succ (nameRank ν)) :=
        ih ν hνc (rank_subname_lt (show ⟨ν, p⟩ₖ ∈ σ from hz))
      have hνo : IsOrdinal (nameRank ν) := isOrdinal_nameRank ν
      have hle : succ (nameRank ν) ⊆ nameRank σ :=
        succ_subset_of_mem_ordinal (nameRank_mem_of_mem_domain hνd)
      exact kpair_mem_iff.mpr
        ⟨nameStage_mono_subset inferInstance hord hle _ hν, hp⟩
    rw [nameStage_succ, nameStageStep]
    exact mem_union_iff.mpr (Or.inr (mem_power_iff.mpr hsub))
  exact key τ (mem_nameClosure_self τ)

/-! ### The bounded classes of names -/

/-- The names over `P` whose name rank belongs to `α`. -/
noncomputable def boundedNames (P α : V) : V :=
  {τ ∈ nameStage P (succ (ordinalSup α)) ; IsForcingName P τ ∧ nameRank τ ∈ α}

theorem mem_boundedNames_iff (P α τ : V) :
    τ ∈ boundedNames P α ↔ IsForcingName P τ ∧ nameRank τ ∈ α := by
  rw [boundedNames, mem_sep_iff]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hord : IsOrdinal (nameRank τ) := isOrdinal_nameRank τ
  have hle : succ (nameRank τ) ⊆ succ (ordinalSup α) :=
    succ_subset_succ_of_subset (subset_ordinalSup hord h.2)
  exact nameStage_mono_subset inferInstance inferInstance hle _
    (mem_nameStage_succ_nameRank h.1)

theorem nameAction_mem_boundedNames {P R π α τ : V} (hπ : IsForcingAutomorphism P R π)
    (h : τ ∈ boundedNames P α) : nameAction π τ ∈ boundedNames P α := by
  obtain ⟨hτ, hr⟩ := (mem_boundedNames_iff P α τ).mp h
  exact (mem_boundedNames_iff P α _).mpr
    ⟨nameAction_isName hπ.1 hτ, by rwa [nameRank_nameAction_of_isName hτ]⟩

/-- The hereditarily symmetric names over `P` whose name rank belongs to `α`. -/
noncomputable def boundedSymmetricNames (P Γ F α : V) : V :=
  {τ ∈ boundedNames P α ; IsHereditarilySymmetricName P Γ F τ}

theorem mem_boundedSymmetricNames_iff (P Γ F α τ : V) :
    τ ∈ boundedSymmetricNames P Γ F α ↔
      IsForcingName P τ ∧ nameRank τ ∈ α ∧ IsHereditarilySymmetricName P Γ F τ := by
  rw [boundedSymmetricNames, mem_sep_iff, mem_boundedNames_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem nameAction_mem_boundedSymmetricNames {P R Γ F π α τ : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hπ : π ∈ Γ) (h : τ ∈ boundedSymmetricNames P Γ F α) :
    nameAction π τ ∈ boundedSymmetricNames P Γ F α := by
  obtain ⟨hτ, hr, hsym⟩ := (mem_boundedSymmetricNames_iff P Γ F α τ).mp h
  refine (mem_boundedSymmetricNames_iff P Γ F α _).mpr
    ⟨nameAction_isName (hΓ.1 π hπ).1 hτ, ?_, ?_⟩
  · rwa [nameRank_nameAction_of_isName hτ]
  · exact (hereditarilySymmetric_nameAction_iff hΓ hF hπ hτ).mpr hsym

/-- Every name lies in one of the bounded classes. -/
theorem exists_nameRank_bound {P τ : V} (hτ : IsForcingName P τ) :
    ∃ α : V, IsOrdinal α ∧ τ ∈ boundedNames P α := by
  have hord : IsOrdinal (nameRank τ) := isOrdinal_nameRank τ
  exact ⟨succ (nameRank τ), inferInstance,
    (mem_boundedNames_iff P _ τ).mpr ⟨hτ, mem_succ_self _⟩⟩

end ZFVP
