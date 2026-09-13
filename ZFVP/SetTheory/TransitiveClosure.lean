import ZFVP.SetTheory.Hierarchy

/-! Internal transitive closure and the definable set-induction schema. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def closureStep (X f : V) : V := X ∪ ⋃ˢ ⋃ˢ range f

instance closureStep_definable (X : V) : ℒₛₑₜ-function₁ (closureStep X) := by
  unfold closureStep
  definability

noncomputable def closureStage (X α : V) : V :=
  Replacement.transfiniteRec (closureStep X) (closureStep_definable X) α

instance closureStage_definable (X : V) : ℒₛₑₜ-function₁ (closureStage X) :=
  Replacement.transfiniteRec_definable (closureStep_definable X)

theorem closureStage_recursion (X : V) (α : Ordinal V) :
    closureStage X (α : V) = closureStep X
      (definableGraph (α : V) (closureStage X) (closureStage_definable X)) :=
  Replacement.transfiniteRec_spec (closureStep X) (closureStep_definable X) α

theorem mem_closureStage_iff (X α x : V) [IsOrdinal α] :
    x ∈ closureStage X α ↔ x ∈ X ∨ ∃ β ∈ α, ∃ y ∈ closureStage X β, x ∈ y := by
  have eqn := closureStage_recursion X (IsOrdinal.toOrdinal α)
  change closureStage X α = _ at eqn
  rw [eqn, closureStep, mem_union_iff, mem_sUnion_iff]
  simp only [mem_sUnion_iff, range_definableGraph, repl_spec]
  constructor
  · rintro (hx | ⟨y, ⟨z, ⟨β, hβ, rfl⟩, hy⟩, hxy⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨β, hβ, y, hy, hxy⟩
  · rintro (hx | ⟨β, hβ, y, hy, hxy⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨y, ⟨closureStage X β, ⟨β, hβ, rfl⟩, hy⟩, hxy⟩

theorem subset_closureStage (X α : V) [IsOrdinal α] : X ⊆ closureStage X α := by
  intro x hx
  exact (mem_closureStage_iff X α x).mpr (Or.inl hx)

theorem union_closureStage_subset_succ (X α : V) [IsOrdinal α] :
    ⋃ˢ closureStage X α ⊆ closureStage X (succ α) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
  exact (mem_closureStage_iff X (succ α) x).mpr
    (Or.inr ⟨α, by simp, y, hy, hxy⟩)

/-- The least transitive set containing every member of X. -/
noncomputable def transitiveClosure (X : V) : V :=
  ⋃ˢ repl (closureStage X) (closureStage_definable X) ω

theorem mem_transitiveClosure_iff (X x : V) :
    x ∈ transitiveClosure X ↔ ∃ n ∈ (ω : V), x ∈ closureStage X n := by
  simp only [transitiveClosure, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨y, ⟨n, hn, rfl⟩, hx⟩
    exact ⟨n, hn, hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨closureStage X n, ⟨n, hn, rfl⟩, hx⟩

theorem subset_transitiveClosure (X : V) : X ⊆ transitiveClosure X := by
  intro x hx
  exact (mem_transitiveClosure_iff X x).mpr
    ⟨∅, empty_mem_ω, subset_closureStage X ∅ x hx⟩

theorem transitiveClosure_transitive (X : V) : IsTransitive (transitiveClosure X) := by
  constructor
  intro x hx y hy
  obtain ⟨n, hn, hxn⟩ := (mem_transitiveClosure_iff X x).mp hx
  have : IsOrdinal n := IsOrdinal.of_mem hn
  apply (mem_transitiveClosure_iff X y).mpr
  refine ⟨succ n, ω_succ_closed hn, ?_⟩
  exact union_closureStage_subset_succ X n y (mem_sUnion_iff.mpr ⟨x, hxn, hy⟩)

theorem closureStage_subset_of_transitive (X T : V) (hXT : X ⊆ T)
    (hT : IsTransitive T) (α : Ordinal V) : closureStage X (α : V) ⊆ T := by
  apply transfinite_induction (fun β ↦ closureStage X β ⊆ T) (by definability) ?_ α
  intro β ih x hx
  rcases (mem_closureStage_iff X (β : V) x).mp hx with hxX | ⟨γ, hγβ, y, hy, hxy⟩
  · exact hXT x hxX
  · have : IsOrdinal γ := IsOrdinal.of_mem hγβ
    have hyT := ih (IsOrdinal.toOrdinal γ) hγβ y hy
    exact hT.transitive y hyT x hxy

theorem transitiveClosure_minimal (X T : V) (hXT : X ⊆ T) (hT : IsTransitive T) :
    transitiveClosure X ⊆ T := by
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_transitiveClosure_iff X x).mp hx
  have : IsOrdinal n := IsOrdinal.of_mem hn
  exact closureStage_subset_of_transitive X T hXT hT (IsOrdinal.toOrdinal n) x hxn

theorem transitiveClosure_characterization (X T : V) :
    T = transitiveClosure X ↔
      IsTransitive T ∧ X ⊆ T ∧ ∀ U : V, IsTransitive U → X ⊆ U → T ⊆ U := by
  constructor
  · rintro rfl
    exact ⟨transitiveClosure_transitive X, subset_transitiveClosure X,
      fun U hU hXU ↦ transitiveClosure_minimal X U hXU hU⟩
  · rintro ⟨hT, hXT, hmin⟩
    exact subset_antisymm
      (hmin _ (transitiveClosure_transitive X) (subset_transitiveClosure X))
      (transitiveClosure_minimal X T hXT hT)

instance transitiveClosure_definable : ℒₛₑₜ-function₁[V] transitiveClosure := by
  suffices ℒₛₑₜ-relation (fun T X : V ↦ T = transitiveClosure X) from this
  have h : ℒₛₑₜ-relation (fun T X : V ↦
      IsTransitive T ∧ X ⊆ T ∧ ∀ U : V, IsTransitive U → X ⊆ U → T ⊆ U) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  exact transitiveClosure_characterization (v 1) (v 0)

/-- ZF set induction for a definable predicate, including set parameters. -/
theorem set_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (step : ∀ x : V, (∀ y ∈ x, P y) → P x) (a : V) : P a := by
  classical
  by_contra ha
  let C := transitiveClosure ({a} : V)
  let bad : V := {x ∈ C ; ¬P x}
  have haC : a ∈ C := subset_transitiveClosure ({a} : V) a (by simp)
  have : IsNonempty bad := ⟨⟨a, by simp [bad, haC, ha]⟩⟩
  obtain ⟨b, hb, hminimal⟩ := foundation bad
  have hb' : b ∈ C ∧ ¬P b := by simpa [bad] using hb
  have hPb : P b := by
    apply step b
    intro y hy
    by_contra hny
    have hyC : y ∈ C := (transitiveClosure_transitive ({a} : V)).transitive b hb'.1 y hy
    have hybad : y ∈ bad := by simp [bad, hyC, hny]
    exact hminimal y hybad hy
  exact hb'.2 hPb

end ZFVP
