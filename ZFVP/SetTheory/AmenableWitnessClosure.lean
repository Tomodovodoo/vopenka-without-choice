import ZFVP.SetTheory.AmenableIteration

/-! Witness closure for formulas in an amenable predicate expansion.
The sequence is an internal omega-function constructed from finite traces. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsNextWitnessStage (R : V → V → Prop) (α β : V) : Prop :=
  IsOrdinal β ∧ rank α ∈ β ∧
    ∀ x ∈ hierarchy α, (∃ y, R x y) → ∃ y ∈ hierarchy β, R x y

namespace IsAmenablePredicate
variable {X : V → Prop} (hX : IsAmenablePredicate X)
include hX

theorem nextWitnessStage_exists (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) (α : V) :
    ∃ β, IsNextWitnessStage R α β := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  let Q (x y : V) := R x y ∨ (¬∃ z, R x z) ∧ y = 0
  have hQ : PredicateExpansion.Rel X Q := by
    change Language.DefinableRel predicateLanguage Q
    unfold Q
    relative_definability X
  obtain ⟨B, hB⟩ := hX.collection (hierarchy α) Q hQ (fun x _ ↦ by
    by_cases hx : ∃ y, R x y
    · obtain ⟨y, hy⟩ := hx
      exact ⟨y, Or.inl hy⟩
    · exact ⟨0, Or.inr ⟨hx, rfl⟩⟩)
  have : IsOrdinal (rank α ∪ rank B) := ordinal_union_ordinal _ _
  refine ⟨succ (rank α ∪ rank B), inferInstance, ?_, ?_⟩
  · apply mem_succ_iff.mpr
    exact IsOrdinal.subset_iff.mp (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))
  · intro x hx hex
    obtain ⟨y, hy, hxy⟩ := hB x hx
    have hsub : rank B ⊆ succ (rank α ∪ rank B) :=
      fun z hz ↦ mem_succ_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inr hz)))
    exact ⟨y, hierarchy_mono hsub y (subset_hierarchy_rank B y hy),
      hxy.resolve_right (fun hh ↦ hh.1 hex)⟩

theorem leastNextWitnessStage_exists (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) (α : V) :
    ∃! β, IsLeastOrdinal (IsNextWitnessStage R α) β := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  have hd : PredicateExpansion.Pred X (IsNextWitnessStage R α) := by
    change Language.DefinablePred predicateLanguage (IsNextWitnessStage R α)
    unfold IsNextWitnessStage
    relative_definability X
  obtain ⟨β, hβ⟩ := hX.nextWitnessStage_exists R hR α
  exact hX.leastOrdinal _ hd ⟨β, hβ.1, hβ⟩

noncomputable def nextWitnessStage (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) (α : V) : V :=
  Classical.choose! (hX.leastNextWitnessStage_exists R hR α)

theorem nextWitnessStage_spec (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) (α : V) :
    IsNextWitnessStage R α (hX.nextWitnessStage R hR α) :=
  (Classical.choose!_spec (hX.leastNextWitnessStage_exists R hR α)).2.1

theorem nextWitnessStage_definable (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) :
    PredicateExpansion.Fun X (hX.nextWitnessStage R hR) := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  have hd : PredicateExpansion.Rel X (fun β α ↦ IsLeastOrdinal (IsNextWitnessStage R α) β) := by
    change Language.DefinableRel predicateLanguage (fun β α : V ↦ IsLeastOrdinal (IsNextWitnessStage R α) β)
    unfold IsLeastOrdinal IsNextWitnessStage
    relative_definability X
  apply Language.Definable.of_iff hd
  intro v
  constructor
  · intro he
    rw [he]
    exact Classical.choose!_spec (hX.leastNextWitnessStage_exists R hR (v 1))
  · intro hh
    exact (hX.leastNextWitnessStage_exists R hR (v 1)).unique hh
      (Classical.choose!_spec (hX.leastNextWitnessStage_exists R hR (v 1)))

/-- The expanded-language version of the reflection closure used in Case II. -/
theorem witnessClosedAbove (R : V → V → Prop) (hR : PredicateExpansion.Rel X R) (γ : V) [IsOrdinal γ] :
    ∃ δ : V, IsOrdinal δ ∧ γ ∈ δ ∧ IsWitnessClosed R δ := by
  let F := hX.nextWitnessStage R hR
  obtain ⟨g, hgf, hgd, hg0, hgs⟩ := hX.iterationGraph_exists F (hX.nextWitnessStage_definable R hR) γ
  have : IsFunction g := hgf
  have hspec (α : V) : IsNextWitnessStage R α (F α) := hX.nextWitnessStage_spec R hR α
  have ha : ∀ n ∈ (ω : V), IsOrdinal (g ‘ n) := by
    apply naturalNumber_induction (fun n ↦ IsOrdinal (g ‘ n)) (by definability)
    · rw [hg0]; infer_instance
    · intro n hn _
      rw [hgs n hn]
      exact (hspec _).1
  have hinc (n : V) (hn : n ∈ (ω : V)) : g ‘ n ∈ g ‘ (succ n) := by
    have : IsOrdinal (g ‘ n) := ha n hn
    rw [hgs n hn]
    simpa only [rank_of_ordinal] using (hspec (g ‘ n)).2.1
  let δ := ⋃ˢ range g
  have hord : IsOrdinal δ := IsOrdinal.sUnion (by
    intro α hα
    obtain ⟨n, hnα⟩ := mem_range_iff.mp hα
    have hn : n ∈ (ω : V) := hgd ▸ mem_domain_of_kpair_mem hnα
    rw [← value_eq_of_kpair_mem hnα]
    exact ha n hn)
  have hstage (n : V) (hn : n ∈ (ω : V)) : g ‘ n ∈ δ := by
    have hs : g ‘ (succ n) ∈ range g := mem_range_of_kpair_mem
      (kpair_value_mem (hgd.symm ▸ ω_succ_closed hn))
    exact mem_sUnion_iff.mpr ⟨g ‘ (succ n), hs, hinc n hn⟩
  have hcof (ξ : V) (hξ : ξ ∈ δ) : ∃ n ∈ (ω : V), ξ ∈ g ‘ n := by
    obtain ⟨α, hα, hξα⟩ := mem_sUnion_iff.mp hξ
    obtain ⟨n, hnα⟩ := mem_range_iff.mp hα
    exact ⟨n, hgd ▸ mem_domain_of_kpair_mem hnα, (value_eq_of_kpair_mem hnα).symm ▸ hξα⟩
  refine ⟨δ, hord, by simpa only [hg0] using hstage 0 (by simp), ?_⟩
  intro x hx hex
  obtain ⟨n, hn, hrank⟩ := hcof (rank x) ((mem_hierarchy_iff_rank_mem _ _).mp hx)
  have : IsOrdinal (g ‘ n) := ha n hn
  obtain ⟨y, hy, hxy⟩ := (hspec (g ‘ n)).2.2 x ((mem_hierarchy_iff_rank_mem _ _).mpr hrank) hex
  rw [← hgs n hn] at hy
  have : IsOrdinal (g ‘ (succ n)) := ha (succ n) (ω_succ_closed hn)
  have : IsOrdinal δ := hord
  have hsub := IsOrdinal.toIsTransitive.transitive _ (hstage (succ n) (ω_succ_closed hn))
  exact ⟨y, hierarchy_mono hsub y hy, hxy⟩

end IsAmenablePredicate
end ZFVP
