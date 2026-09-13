import ZFVP.SetTheory.SupercompactMeasure

/-! # Normality for functions whose values need not lie below `lam`

`IsNormalFineMeasure κ lam U` carries the normality clause `IsNormalOn κ lam U`, which speaks
only about functions in `lam ^ P_κ(lam)`. The internal ultrapower meets functions on `P_κ(lam)`
whose values live in a rank stage and happen to be regressive on a set of measure one. This
module gives normality in that form.

The bridge is `trimTo lam f`, the function sending `x` to `f ‘ x` when that value lies in `lam`
and to `∅` otherwise. It is written as a union of a separation rather than with a case split, so
that the `definability` tactic can see it. Feeding its graph to `IsNormalOn` and intersecting the
resulting constant set with the regressive set of `f` transfers the conclusion back to `f`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The value `f ‘ x` cut down to `lam`: it is `f ‘ x` when `f ‘ x ∈ lam`, and `∅` otherwise. -/
noncomputable def trimTo (lam f x : V) : V := ⋃ˢ {z ∈ lam ; z = f ‘ x}

theorem trimTo_definable_one (lam f : V) : ℒₛₑₜ-function₁[V] (trimTo lam f) := by
  have h : ℒₛₑₜ-relation[V] (fun y x ↦ ∀ w, w ∈ y ↔ ∃ z, (z ∈ lam ∧ z = f ‘ x) ∧ w ∈ z) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = trimTo lam f (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [trimTo, mem_sUnion_iff, mem_sep_iff]

/-- On the values that already lie in `lam`, `trimTo` changes nothing. -/
theorem trimTo_eq {lam f x : V} (h : f ‘ x ∈ lam) : trimTo lam f x = f ‘ x := by
  apply mem_ext
  intro w
  simp only [trimTo, mem_sUnion_iff, mem_sep_iff]
  constructor
  · rintro ⟨z, ⟨-, rfl⟩, hw⟩
    exact hw
  · intro hw
    exact ⟨f ‘ x, ⟨h, rfl⟩, hw⟩

/-- Off those values, `trimTo` is `∅`. -/
theorem trimTo_eq_empty {lam f x : V} (h : f ‘ x ∉ lam) : trimTo lam f x = (∅ : V) := by
  apply mem_ext
  intro w
  simp only [trimTo, mem_sUnion_iff, mem_sep_iff, not_mem_empty, iff_false, not_exists]
  rintro z ⟨⟨hz, rfl⟩, -⟩
  exact h hz

/-- `trimTo lam f` maps everything into `lam` as soon as `∅ ∈ lam`. -/
theorem trimTo_mem {lam f x : V} (h0 : (∅ : V) ∈ lam) : trimTo lam f x ∈ lam := by
  by_cases h : f ‘ x ∈ lam
  · rw [trimTo_eq h]; exact h
  · rw [trimTo_eq_empty h]; exact h0

/-- Every member of `P_κ(lam)` is a subset of `lam`, so a regressive value lies below `lam`. -/
theorem regressive_value_mem {κ lam x y : V} (hx : x ∈ smallSubsetsBelow κ lam) (hy : y ∈ x) :
    y ∈ lam :=
  ((mem_smallSubsetsBelow_iff κ lam x).mp hx).1 y hy

/-- Fineness in the form the ultrapower uses. -/
theorem normalFineMeasure_fine {κ lam U ξ : V} (hU : IsNormalFineMeasure κ lam U) (hξ : ξ ∈ lam) :
    {x ∈ smallSubsetsBelow κ lam ; ξ ∈ x} ∈ U :=
  hU.2.2.1 ξ hξ

/-- Normality for a function with arbitrary values: if a function on `P_κ(lam)` sends almost every
`x` into `x`, it is constant on a set of measure one, with a value below `lam`. -/
theorem normalFineMeasure_regressive_constant {κ lam U f : V} (hU : IsNormalFineMeasure κ lam U)
    (h0 : (∅ : V) ∈ lam) (hf : IsFunction f) (hdom : domain f = smallSubsetsBelow κ lam)
    (hreg : {x ∈ smallSubsetsBelow κ lam ; f ‘ x ∈ x} ∈ U) :
    ∃ ξ ∈ lam, {x ∈ smallSubsetsBelow κ lam ; f ‘ x = ξ} ∈ U := by
  have hGd : ℒₛₑₜ-function₁[V] (trimTo lam f) := trimTo_definable_one lam f
  -- the replacement function, an honest member of `lam ^ P_κ(lam)`
  set g : V := definableGraph (smallSubsetsBelow κ lam) (trimTo lam f) hGd with hgdef
  have hgmem : g ∈ lam ^ (smallSubsetsBelow κ lam) :=
    definableGraph_mem_function_of_mapsTo _ _ _ hGd (fun _ _ ↦ trimTo_mem h0)
  have hgval : ∀ x ∈ smallSubsetsBelow κ lam, g ‘ x = trimTo lam f x :=
    fun _ hx ↦ value_definableGraph _ _ hGd hx
  -- on the regressive set of `f`, `g` agrees with `f`
  have hagree : ∀ x ∈ smallSubsetsBelow κ lam, f ‘ x ∈ x → g ‘ x = f ‘ x := by
    intro x hx hxr
    rw [hgval x hx, trimTo_eq (regressive_value_mem hx hxr)]
  -- so the regressive set of `g` contains that of `f`
  have hregg : {x ∈ smallSubsetsBelow κ lam ; g ‘ x ∈ x} ∈ U := by
    refine hU.upward hreg (fun x hx ↦ (mem_sep_iff.mp hx).1) ?_
    intro x hx
    obtain ⟨hxP, hxr⟩ := mem_sep_iff.mp hx
    exact mem_sep_iff.mpr ⟨hxP, by rw [hagree x hxP hxr]; exact hxr⟩
  obtain ⟨ξ, hξ, hS⟩ := hU.2.2.2 g hgmem hregg
  refine ⟨ξ, hξ, ?_⟩
  refine hU.upward (hU.1.2.2.2.2.1 _ hS _ hreg) (fun x hx ↦ (mem_sep_iff.mp hx).1) ?_
  intro x hx
  obtain ⟨h1, h2⟩ := mem_inter_iff.mp hx
  obtain ⟨hxP, hxg⟩ := mem_sep_iff.mp h1
  obtain ⟨-, hxr⟩ := mem_sep_iff.mp h2
  exact mem_sep_iff.mpr ⟨hxP, by rw [← hagree x hxP hxr]; exact hxg⟩

end ZFVP
