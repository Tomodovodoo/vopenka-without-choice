import ZFVP.SetTheory.TransitiveClosure

/-! Rank in an arbitrary internal ZF model. The proof of existence uses
definable set induction and Replacement of unique least ordinal witnesses.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastOrdinal (P : V → Prop) (α : V) : Prop :=
  IsOrdinal α ∧ P α ∧ ∀ β : V, IsOrdinal β → P β → α ⊆ β

theorem leastOrdinal_existsUnique (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hex : ∃ α : V, IsOrdinal α ∧ P α) : ∃! α, IsLeastOrdinal P α := by
  obtain ⟨α, hα, hPα⟩ := hex
  have : IsOrdinal α := hα
  obtain ⟨β, hβ, hmin⟩ := exists_minimal P hP ⟨IsOrdinal.toOrdinal α, hPα⟩
  refine ⟨(β : V), ⟨β.ordinal, hβ, ?_⟩, ?_⟩
  · intro γ hγ hPγ
    have : IsOrdinal γ := hγ
    exact hmin (IsOrdinal.toOrdinal γ) hPγ
  · intro γ hγ
    have : IsOrdinal γ := hγ.1
    exact subset_antisymm (hγ.2.2 β β.ordinal hβ)
      (hmin (IsOrdinal.toOrdinal γ) hγ.2.1)

def IsLeastContainingStage (x α : V) : Prop :=
  IsLeastOrdinal (fun β ↦ x ∈ hierarchy β) α

instance isLeastContainingStage_definable : ℒₛₑₜ-relation[V] IsLeastContainingStage := by
  unfold IsLeastContainingStage IsLeastOrdinal
  definability

/-- Every internal set is contained in an internal cumulative stage. -/
theorem hierarchy_bound_exists (x : V) : ∃ α : V, IsOrdinal α ∧ x ⊆ hierarchy α := by
  apply set_induction (fun y : V ↦ ∃ α : V, IsOrdinal α ∧ y ⊆ hierarchy α)
    (by definability) ?_ x
  intro y ih
  have hw : ∀ z ∈ y, ∃! α, IsLeastContainingStage z α := by
    intro z hzy
    obtain ⟨β, hβ, hzβ⟩ := ih z hzy
    have : IsOrdinal β := hβ
    apply leastOrdinal_existsUnique (fun α ↦ z ∈ hierarchy α) (by definability)
    refine ⟨succ β, inferInstance, ?_⟩
    rw [hierarchy_succ, mem_power_iff]
    exact hzβ
  obtain ⟨B, hB⟩ := replacement_rel_exists_of_mem_existsUnique y
    IsLeastContainingStage hw isLeastContainingStage_definable
  have hBord : ∀ β ∈ B, IsOrdinal β := by
    intro β hβB
    obtain ⟨z, _, hzβ⟩ := (hB β).mp hβB
    exact hzβ.1
  have hκ : IsOrdinal (⋃ˢ B) := IsOrdinal.sUnion hBord
  refine ⟨⋃ˢ B, hκ, ?_⟩
  intro z hzy
  obtain ⟨β, hzβ, _⟩ := hw z hzy
  have hβB : β ∈ B := (hB β).mpr ⟨z, hzy, hzβ⟩
  have : IsOrdinal β := hzβ.1
  exact hierarchy_mono (subset_sUnion_of_mem hβB) z hzβ.2.1

def IsRank (x α : V) : Prop :=
  IsLeastOrdinal (fun β ↦ x ⊆ hierarchy β) α

instance isRank_definable : ℒₛₑₜ-relation[V] IsRank := by
  unfold IsRank IsLeastOrdinal
  definability

theorem rank_existsUnique (x : V) : ∃! α, IsRank x α :=
  leastOrdinal_existsUnique (fun α ↦ x ⊆ hierarchy α) (by definability)
    (hierarchy_bound_exists x)

/-- Rank is the least ordinal alpha such that x is a subset of V_alpha. -/
noncomputable def rank (x : V) : V := Classical.choose! (rank_existsUnique x)

theorem rank_spec (x : V) : IsRank x (rank x) :=
  Classical.choose!_spec (rank_existsUnique x)

instance rank_ordinal (x : V) : IsOrdinal (rank x) := (rank_spec x).1

theorem subset_hierarchy_rank (x : V) : x ⊆ hierarchy (rank x) := (rank_spec x).2.1

theorem rank_minimal (x α : V) (hα : IsOrdinal α) (hx : x ⊆ hierarchy α) :
    rank x ⊆ α := (rank_spec x).2.2 α hα hx

theorem rank_eq_iff (x α : V) : rank x = α ↔ IsRank x α := by
  constructor
  · rintro rfl
    exact rank_spec x
  · intro hα
    exact ((rank_existsUnique x).unique hα (rank_spec x)).symm

instance rank_definable : ℒₛₑₜ-function₁[V] rank := by
  suffices ℒₛₑₜ-relation (fun α x : V ↦ α = rank x) from this
  have h : ℒₛₑₜ-relation (fun α x : V ↦ IsRank x α) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (rank_eq_iff (v 1) (v 0))

theorem mem_hierarchy_iff_rank_mem (x α : V) [IsOrdinal α] :
    x ∈ hierarchy α ↔ rank x ∈ α := by
  constructor
  · intro hx
    obtain ⟨β, hβα, hxβ⟩ := (mem_hierarchy_iff_of_ordinal α x).mp hx
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    have hle := rank_minimal x β inferInstance hxβ
    rcases IsOrdinal.subset_iff.mp hle with heq | hlt
    · exact heq ▸ hβα
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hβα
  · intro hx
    exact (mem_hierarchy_iff_of_ordinal α x).mpr ⟨rank x, hx, subset_hierarchy_rank x⟩

theorem rank_mono {x y : V} (hxy : x ⊆ y) : rank x ⊆ rank y :=
  rank_minimal x (rank y) inferInstance (subset_trans hxy (subset_hierarchy_rank y))

theorem rank_mem {x y : V} (hxy : x ∈ y) : rank x ∈ rank y :=
  (mem_hierarchy_iff_rank_mem x (rank y)).mp (subset_hierarchy_rank y x hxy)

theorem rank_empty : rank (∅ : V) = ∅ := by
  exact subset_empty_iff_eq_empty.mp (rank_minimal ∅ ∅ inferInstance (empty_subset _))

theorem rank_hierarchy (α : V) [IsOrdinal α] : rank (hierarchy α) = α := by
  have hle := rank_minimal (hierarchy α) α inferInstance (subset_refl _)
  rcases IsOrdinal.subset_iff.mp hle with heq | hlt
  · exact heq
  · have hmem := hierarchy_mem hlt
    have hbad := subset_hierarchy_rank (hierarchy α) _ hmem
    exact False.elim (mem_irrefl _ hbad)

end ZFVP
