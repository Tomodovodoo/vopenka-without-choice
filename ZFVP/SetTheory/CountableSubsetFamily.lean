import ZFVP.SetTheory.SchroederBernstein
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! The family of countably enumerated subsets of a set.

`countableSubsets lam` collects the ranges of the internal functions `ω → lam`, that is the
subsets of `lam` that carry an internal enumeration by `ω`. `countableSubsetsOf lam A` cuts that
family down to the subsets of `A`.

This is the index family of the Erdos-Hajnal construction of omega-Jonsson functions: the domain
of such a function is a set of countably enumerated subsets, and the two cardinality facts proved
here are the ones the construction uses. If `lam` injects into a subset `A ⊆ lam`, then
`countableSubsets lam` injects into the part of it living inside `A`, by taking images along the
injection. And `lam` itself injects into `countableSubsets lam` by singletons. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The set of subsets of `lam` that are the range of an internal function `ω → lam`. -/
noncomputable def countableSubsets (lam : V) : V :=
  repl range (by definability) (lam ^ (ω : V))

theorem mem_countableSubsets_iff {lam a : V} :
    a ∈ countableSubsets lam ↔ ∃ g, g ∈ lam ^ (ω : V) ∧ range g = a := by
  simp only [countableSubsets, repl_spec]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem countableSubsets_subset {lam a : V} (ha : a ∈ countableSubsets lam) : a ⊆ lam := by
  obtain ⟨g, hg, rfl⟩ := mem_countableSubsets_iff.mp ha
  exact range_subset_of_mem_function hg

/-- An enumeration of `a` by `ω` puts `a` into `countableSubsets lam` as soon as `a ⊆ lam`. -/
theorem mem_countableSubsets_of_enumeration {lam a g : V} (ha : a ⊆ lam)
    (hg : g ∈ a ^ (ω : V)) (hr : range g = a) : a ∈ countableSubsets lam :=
  mem_countableSubsets_iff.mpr ⟨g, mem_function_of_mem_function_of_subset hg ha, hr⟩

/-- A member of `countableSubsets lam` has an enumeration onto itself, not merely one into `lam`. -/
theorem exists_enumeration_of_mem_countableSubsets {lam a : V} (ha : a ∈ countableSubsets lam) :
    ∃ g, g ∈ a ^ (ω : V) ∧ range g = a := by
  obtain ⟨g, hg, hr⟩ := mem_countableSubsets_iff.mp ha
  have hgf : IsFunction g := IsFunction.of_mem hg
  refine ⟨g, ?_, hr⟩
  have h := isFunction_iff.mp hgf
  rw [hr, domain_eq_of_mem_function hg] at h
  exact h

/-- The countably enumerated subsets of `lam` that are contained in `A`. -/
noncomputable def countableSubsetsOf (lam A : V) : V := {a ∈ countableSubsets lam ; a ⊆ A}

theorem mem_countableSubsetsOf_iff {lam A a : V} :
    a ∈ countableSubsetsOf lam A ↔ a ∈ countableSubsets lam ∧ a ⊆ A := by
  simp only [countableSubsetsOf, mem_sep_iff]

/-- Taking images along an injection `lam → A` sends a countably enumerated subset of `lam` to a
countably enumerated subset of `A`. -/
private theorem range_compose_eq_graphImage {g i : V} :
    range (compose g i) = graphImage i (range g) := by
  apply SetTheory.subset_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := mem_range_iff.mp hy
    obtain ⟨w, hxw, hwy⟩ := kpair_mem_compose_iff.mp hx
    exact (mem_graphImage_iff i (range g) y).mpr ⟨w, mem_range_of_kpair_mem hxw, hwy⟩
  · intro y hy
    obtain ⟨w, hw, hwy⟩ := (mem_graphImage_iff i (range g) y).mp hy
    obtain ⟨x, hxw⟩ := mem_range_iff.mp hw
    exact mem_range_of_kpair_mem (kpair_mem_compose_iff.mpr ⟨w, hxw, hwy⟩)

/-- If `lam` injects into a subset `A` of `lam`, then every countably enumerated subset of `lam`
has a countably enumerated image inside `A`, and distinct subsets have distinct images. -/
theorem countableSubsets_cardLE_countableSubsetsOf {lam A : V} (hA : A ⊆ lam) (h : lam ≤# A) :
    countableSubsets lam ≤# countableSubsetsOf lam A := by
  obtain ⟨i, hi, hinj⟩ := h
  have hif : IsFunction i := IsFunction.of_mem hi
  have hdom : domain i = lam := domain_eq_of_mem_function hi
  refine cardLE_of_injective_map (fun a ↦ graphImage i a) (by definability) ?_ ?_
  · intro a ha
    obtain ⟨g, hg, rfl⟩ := mem_countableSubsets_iff.mp ha
    refine mem_countableSubsetsOf_iff.mpr ⟨?_, graphImage_subset hi⟩
    refine mem_countableSubsets_iff.mpr ⟨compose g i, ?_, range_compose_eq_graphImage⟩
    exact mem_function_of_mem_function_of_subset (compose_function hg hi) hA
  · have key : ∀ u v : V, u ∈ countableSubsets lam →
        graphImage i u = graphImage i v → u ⊆ v := by
      intro u v hu he x hx
      have hxd : x ∈ domain i := by rw [hdom]; exact countableSubsets_subset hu x hx
      have hpair : ⟨x, i ‘ x⟩ₖ ∈ i := kpair_value_mem hxd
      have hmem : i ‘ x ∈ graphImage i v :=
        he ▸ (mem_graphImage_iff i u (i ‘ x)).mpr ⟨x, hx, hpair⟩
      obtain ⟨x', hx'v, hx'⟩ := (mem_graphImage_iff i v (i ‘ x)).mp hmem
      have : x' = x := hinj x' x (i ‘ x) hx' hpair
      exact this ▸ hx'v
    intro a ha b hb heq
    exact SetTheory.subset_antisymm (key a b ha heq) (key b a hb heq.symm)

/-- `lam` injects into its family of countably enumerated subsets, by singletons. -/
theorem cardLE_countableSubsets {lam : V} [IsOrdinal lam] (hω : (ω : V) ∈ lam) :
    lam ≤# countableSubsets lam := by
  refine cardLE_of_injective_map (fun γ ↦ ({γ} : V)) (by definability) ?_ ?_
  · intro γ hγ
    have hsub : ({γ} : V) ⊆ lam := by
      intro z hz
      rw [mem_singleton_iff] at hz
      exact hz ▸ hγ
    have hdef : ℒₛₑₜ-function₁[V] (fun _ : V ↦ γ) := by definability
    refine mem_countableSubsets_of_enumeration hsub
      (g := definableGraph (ω : V) (fun _ ↦ γ) hdef) ?_ ?_
    · exact definableGraph_mem_function_of_mapsTo (ω : V) ({γ} : V) (fun _ ↦ γ) hdef
        (fun _ _ ↦ mem_singleton_iff.mpr rfl)
    · rw [range_definableGraph]
      apply SetTheory.subset_antisymm
      · intro y hy
        obtain ⟨_, _, rfl⟩ := (repl_spec hdef).mp hy
        exact mem_singleton_iff.mpr rfl
      · intro y hy
        rw [mem_singleton_iff] at hy
        exact (repl_spec hdef).mpr ⟨∅, empty_mem_ω, hy⟩
  · intro γ _ δ _ he
    have : γ ∈ ({δ} : V) := he ▸ mem_singleton_iff.mpr rfl
    exact mem_singleton_iff.mp this

end ZFVP
