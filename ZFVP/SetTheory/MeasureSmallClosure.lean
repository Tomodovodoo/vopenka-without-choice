import ZFVP.SetTheory.SupercompactMeasure
import ZFVP.SetTheory.InverseFunction

/-! # Two working consequences of a normal fine measure

`IsOrdinalCompleteOn` states completeness for families given by a set function `g ∈ U ^ α`.
Users of the measure usually have a family given by a definable operation `F : V → V` instead.
The first theorem here bridges that gap: it replaces `g` by `definableGraph α F hF`.

The second theorem says that for a fixed `a ∈ P_κ(lam)` almost every `x ∈ P_κ(lam)` contains
`a`. This is fineness upgraded from single points to small sets, and it is where completeness
below `κ` is used: `a` injects into an ordinal `μ ∈ κ`, so `a ⊆ x` is an intersection of `μ`
many conditions, each of which holds almost everywhere by fineness.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Completeness for a definable family indexed by an ordinal below `κ`. -/
theorem normalFineMeasure_definable_intersection {κ lam U α : V} (hU : IsNormalFineMeasure κ lam U)
    (hα : α ∈ κ) (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hmem : ∀ i ∈ α, F i ∈ U) :
    {x ∈ smallSubsetsBelow κ lam ; ∀ i ∈ α, x ∈ F i} ∈ U := by
  have hg : definableGraph α F hF ∈ U ^ α :=
    definableGraph_mem_function_of_mapsTo α U F hF hmem
  have hint := hU.2.1 α hα _ hg
  have heq : indexedIntersection (smallSubsetsBelow κ lam) α (definableGraph α F hF)
      = {x ∈ smallSubsetsBelow κ lam ; ∀ i ∈ α, x ∈ F i} := by
    apply mem_ext
    intro z
    rw [mem_indexedIntersection_iff, mem_sep_iff]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun i hi ↦ ?_⟩
      have := h i hi
      rwa [value_definableGraph α F hF hi] at this
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun i hi ↦ ?_⟩
      rw [value_definableGraph α F hF hi]
      exact h i hi
  rwa [heq] at hint

/-- Almost every member of `P_κ(lam)` contains a given subset of `lam` of size below `κ`. -/
theorem normalFineMeasure_small_subset {κ lam U a : V} (hU : IsNormalFineMeasure κ lam U)
    (ha : a ∈ smallSubsetsBelow κ lam) :
    {x ∈ smallSubsetsBelow κ lam ; a ⊆ x} ∈ U := by
  obtain ⟨hasub, μ, hμ, e, he, hinj⟩ := (mem_smallSubsetsBelow_iff _ _ _).mp ha
  set F : V → V := fun i ↦ {x ∈ smallSubsetsBelow κ lam ; ∀ z ∈ a, e ‘ z = i → z ∈ x} with hFdef
  have hF : ℒₛₑₜ-function₁[V] F := by
    have hd : ℒₛₑₜ-relation[V] (fun Y i ↦ ∀ x, x ∈ Y ↔
        x ∈ smallSubsetsBelow κ lam ∧ ∀ z ∈ a, e ‘ z = i → z ∈ x) := by definability
    apply Language.Definable.of_iff hd
    intro v
    change v 0 = F (v 1) ↔ _
    rw [mem_ext_iff]
    simp only [hFdef, mem_sep_iff]
  have hFsub (i : V) : F i ⊆ smallSubsetsBelow κ lam := by
    intro x hx
    exact (mem_sep_iff.mp hx).1
  have hmem : ∀ i ∈ μ, F i ∈ U := by
    intro i _
    by_cases hex : ∃ z ∈ a, e ‘ z = i
    · obtain ⟨z, hz, hzi⟩ := hex
      refine hU.upward (hU.2.2.1 z (hasub z hz)) (hFsub i) ?_
      intro x hx
      obtain ⟨hxP, hzx⟩ := mem_sep_iff.mp hx
      refine mem_sep_iff.mpr ⟨hxP, fun w hw hwi ↦ ?_⟩
      have : w = z := injective_value_eq he hinj hw hz (by rw [hwi, hzi])
      rw [this]
      exact hzx
    · refine hU.upward hU.base_mem (hFsub i) ?_
      intro x hx
      exact mem_sep_iff.mpr ⟨hx, fun w hw hwi ↦ absurd ⟨w, hw, hwi⟩ hex⟩
  have hbig := normalFineMeasure_definable_intersection hU hμ F hF hmem
  refine hU.upward hbig (fun x hx ↦ (mem_sep_iff.mp hx).1) ?_
  intro x hx
  obtain ⟨hxP, hall⟩ := mem_sep_iff.mp hx
  refine mem_sep_iff.mpr ⟨hxP, fun z hz ↦ ?_⟩
  have hval : e ‘ z ∈ μ := function_value_mem he hz
  have := hall (e ‘ z) hval
  exact (mem_sep_iff.mp this).2 z hz rfl

end ZFVP
