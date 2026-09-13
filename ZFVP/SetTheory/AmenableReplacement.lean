import ZFVP.SetTheory.AmenableSeparation
import ZFVP.SetTheory.WitnessClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace IsAmenablePredicate
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  {X : V → Prop} (hX : IsAmenablePredicate X)
include hX

theorem replacementOn (A : V) (R : V → V → Prop) (hR : PredicateExpansion.Rel X R)
    (h : ∀ x ∈ A, ∃! y, R x y) : ∃ B : V, ∀ y, y ∈ B ↔ ∃ x ∈ A, R x y := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  let Q (x y : V) := (x ∈ A ∧ R x y) ∨ (x ∉ A ∧ y = 0)
  have hQ : PredicateExpansion.Rel X Q := by
    change Language.DefinableRel predicateLanguage Q
    unfold Q
    relative_definability X
  have huniq : ∀ x, ∃! y, Q x y := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨y, hy, hu⟩ := h x hx
      exact ⟨y, Or.inl ⟨hx, hy⟩, fun z hz ↦ hu z ((hz.resolve_right (fun hh ↦ hh.1 hx)).2)⟩
    · exact ⟨0, Or.inr ⟨hx, rfl⟩, fun z hz ↦ (hz.resolve_left (fun hh ↦ hx hh.1)).2⟩
  obtain ⟨B, hB⟩ := hX.replacement Q hQ huniq A
  refine ⟨B, fun y ↦ (hB y).trans ?_⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (hxy.resolve_right (fun hh ↦ hh.1 hx)).2⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Or.inl ⟨hx, hxy⟩⟩

theorem functionReplacement (A : V) (F : V → V) (hF : PredicateExpansion.Fun X F) :
    ∃ B : V, ∀ y, y ∈ B ↔ ∃ x ∈ A, y = F x := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableFunction₁ predicateLanguage F := hF
  apply hX.replacement (fun x y ↦ y = F x) ?_ (fun x ↦ ⟨F x, rfl, fun _ h ↦ h⟩) A
  change Language.DefinableRel predicateLanguage (fun x y : V ↦ y = F x)
  exact Language.Definable.retraction hF ![1, 0]

theorem leastWitnessStage (R : V → V → Prop) (hR : PredicateExpansion.Rel X R)
    (x : V) (hex : ∃ y, R x y) : ∃! α, IsLeastWitnessStage R x α := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  obtain ⟨y, hy⟩ := hex
  apply hX.leastOrdinal (fun β ↦ ∃ z ∈ hierarchy β, R x z) ?_
    ⟨succ (rank y), inferInstance, y, ?_, hy⟩
  · change Language.DefinablePred predicateLanguage (fun β : V ↦ ∃ z ∈ hierarchy β, R x z)
    relative_definability X
  · rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank y

theorem collection (A : V) (R : V → V → Prop) (hR : PredicateExpansion.Rel X R)
    (h : ∀ x ∈ A, ∃ y, R x y) : ∃ B : V, ∀ x ∈ A, ∃ y ∈ B, R x y := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage R := hR
  have hw := fun x hx ↦ hX.leastWitnessStage R hR x (h x hx)
  have hd : PredicateExpansion.Rel X (IsLeastWitnessStage R) := by
    change Language.DefinableRel predicateLanguage (IsLeastWitnessStage R)
    unfold IsLeastWitnessStage IsLeastOrdinal
    relative_definability X
  obtain ⟨C, hC⟩ := hX.replacementOn A (IsLeastWitnessStage R) hd hw
  have : IsOrdinal (⋃ˢ C) := IsOrdinal.sUnion (by
    intro α hα
    obtain ⟨x, _, hx⟩ := (hC α).mp hα
    exact hx.1)
  refine ⟨hierarchy (⋃ˢ C), ?_⟩
  intro x hx
  obtain ⟨α, hα, _⟩ := hw x hx
  obtain ⟨y, hy, hxy⟩ := hα.2.1
  have : IsOrdinal α := hα.1
  exact ⟨y, hierarchy_mono (subset_sUnion_of_mem ((hC α).mpr ⟨x, hx, hα⟩)) y hy, hxy⟩

end IsAmenablePredicate
end ZFVP
