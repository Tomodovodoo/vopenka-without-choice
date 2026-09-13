import ZFVP.SetTheory.InternalTranspositions
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.SymmetricSystems

/-! Permutations of `ω × ω` preserving the first coordinate: each column is permuted
separately. A finite set of coordinates above column `n` can be moved off any finite
set by a column permutation fixing the first `n` columns pointwise. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The coordinate set: pairs of a column and a position. -/
noncomputable abbrev columnCoordinates (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  (ω : V) ×ˢ (ω : V)

def IsColumnPermutation (π : V) : Prop :=
  IsInternalPermutation (columnCoordinates V) π ∧
    ∀ z ∈ columnCoordinates V, kpair.π₁ (π ‘ z) = kpair.π₁ z

instance isColumnPermutation_definable : ℒₛₑₜ-predicate[V] IsColumnPermutation := by
  unfold IsColumnPermutation
  definability

noncomputable def columnPermutations (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {π ∈ internalPermutations (columnCoordinates V) ; ∀ z ∈ columnCoordinates V, kpair.π₁ (π ‘ z) = kpair.π₁ z}

theorem mem_columnPermutations (π : V) : π ∈ columnPermutations V ↔ IsColumnPermutation π := by
  simp only [columnPermutations, mem_sep_iff, mem_internalPermutations, IsColumnPermutation]

theorem IsColumnPermutation.identity : IsColumnPermutation (identity (columnCoordinates V)) :=
  ⟨internalPermutation_identity _, fun z hz ↦ by rw [identity_value hz]⟩

theorem IsColumnPermutation.comp {π ρ : V} (hπ : IsColumnPermutation π) (hρ : IsColumnPermutation ρ) :
    IsColumnPermutation (compose π ρ) := by
  refine ⟨hπ.1.comp hρ.1, fun z hz ↦ ?_⟩
  rw [value_compose_of_mem_function hπ.1.1 hρ.1.1 hz, hρ.2 _ (function_value_mem hπ.1.1 hz), hπ.2 z hz]

theorem IsColumnPermutation.inv {π : V} (hπ : IsColumnPermutation π) :
    IsColumnPermutation (converseGraph π) := by
  refine ⟨hπ.1.inv, fun z hz ↦ ?_⟩
  have hw : (converseGraph π) ‘ z ∈ columnCoordinates V := function_value_mem hπ.1.inv.1 hz
  have hcol := hπ.2 _ hw
  rw [hπ.1.value_inv hz] at hcol
  exact hcol.symm

theorem columnPermutations_group :
    IsForcingAutomorphismGroup (columnCoordinates V) ∅ (columnPermutations V) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro π hπ
    exact (internalPermutation_iff_emptyOrder _ π).mp ((mem_columnPermutations π).mp hπ).1
  · exact (mem_columnPermutations _).mpr IsColumnPermutation.identity
  · intro π hπ ρ hρ
    exact (mem_columnPermutations _).mpr
      (((mem_columnPermutations π).mp hπ).comp ((mem_columnPermutations ρ).mp hρ))
  · intro π hπ
    exact (mem_columnPermutations _).mpr ((mem_columnPermutations π).mp hπ).inv

/-- A column permutation fixing every coordinate of the first `n` columns. -/
def FixesColumnsBelow (n π : V) : Prop := ∀ z ∈ columnCoordinates V, kpair.π₁ z ∈ n → π ‘ z = z

theorem IsColumnPermutation.value_mem {π z : V} (hπ : IsColumnPermutation π)
    (hz : z ∈ columnCoordinates V) : π ‘ z ∈ columnCoordinates V := function_value_mem hπ.1.1 hz

theorem columnTransposition_isColumnPermutation {m k k' : V} (hm : m ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hk' : k' ∈ (ω : V)) :
    IsColumnPermutation (internalTransposition (columnCoordinates V) ⟨m, k⟩ₖ ⟨m, k'⟩ₖ) := by
  have ha : ⟨m, k⟩ₖ ∈ columnCoordinates V := kpair_mem_iff.mpr ⟨hm, hk⟩
  have hb : ⟨m, k'⟩ₖ ∈ columnCoordinates V := kpair_mem_iff.mpr ⟨hm, hk'⟩
  refine ⟨internalTransposition_permutation ha hb, fun z hz ↦ ?_⟩
  classical
  by_cases hza : z = ⟨m, k⟩ₖ
  · subst hza
    rw [internalTransposition_left ha]
    simp
  · by_cases hzb : z = ⟨m, k'⟩ₖ
    · subst hzb
      rw [internalTransposition_right hb]
      simp
    · rw [internalTransposition_fixed hz hza hzb]

/-- A finite set of coordinates above column `n` can be moved off a finite set `Y` by a column
permutation that fixes the first `n` columns pointwise. -/
theorem exists_columnPermutation_moving {n X Y : V}
    (hX : IsInternallyFinite X) (hXc : X ⊆ columnCoordinates V)
    (hXn : ∀ z ∈ X, kpair.π₁ z ∉ n) (hY : IsInternallyFinite Y) :
    ∃ π, IsColumnPermutation π ∧ FixesColumnsBelow n π ∧ ∀ z ∈ X, π ‘ z ∉ Y := by
  classical
  suffices h : ∀ X : V, IsInternallyFinite X → IsInternallyFinite X ∧
      (X ⊆ columnCoordinates V → (∀ z ∈ X, kpair.π₁ z ∉ n) →
        ∃ π, IsColumnPermutation π ∧ FixesColumnsBelow n π ∧ ∀ z ∈ X, π ‘ z ∉ Y) from
    (h X hX).2 hXc hXn
  apply internallyFinite_induction
    (fun X ↦ IsInternallyFinite X ∧ (X ⊆ columnCoordinates V → (∀ z ∈ X, kpair.π₁ z ∉ n) →
      ∃ π, IsColumnPermutation π ∧ FixesColumnsBelow n π ∧ ∀ z ∈ X, π ‘ z ∉ Y))
    (by definability)
  · refine ⟨internallyFinite_empty, fun _ _ ↦ ?_⟩
    exact ⟨identity (columnCoordinates V), IsColumnPermutation.identity,
      fun z hz _ ↦ identity_value hz, fun z hz ↦ (not_mem_empty hz).elim⟩
  · intro C c ih
    refine ⟨internallyFinite_insert ih.1 c, fun hCc hCn ↦ ?_⟩
    have hCfin := ih.1
    obtain ⟨π₀, hπ₀, hfix₀, hmove₀⟩ := ih.2 (fun z hz ↦ hCc z (mem_insert.mpr (Or.inr hz)))
      (fun z hz ↦ hCn z (mem_insert.mpr (Or.inr hz)))
    have hc : c ∈ columnCoordinates V := hCc c (mem_insert.mpr (Or.inl rfl))
    have hcn : kpair.π₁ c ∉ n := hCn c (mem_insert.mpr (Or.inl rfl))
    obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hc
    simp only [kpair.π₁_kpair] at hcn
    have hw : π₀ ‘ ⟨m, k⟩ₖ ∈ columnCoordinates V := hπ₀.value_mem hc
    obtain ⟨m₁, hm₁, k₁, hk₁, hw'⟩ := mem_prod_iff.mp hw
    have hcol : m₁ = m := by
      have := hπ₀.2 _ hc
      rw [hw'] at this
      simpa using this
    subst hcol
    by_cases hwY : π₀ ‘ ⟨m₁, k⟩ₖ ∉ Y
    · refine ⟨π₀, hπ₀, hfix₀, fun z hz ↦ ?_⟩
      rcases mem_insert.mp hz with rfl | hz
      · exact hwY
      · exact hmove₀ z hz
    · -- move the image of `c` to a fresh position in its column
      let used : V := repl kpair.π₂ (by definability)
        ({z ∈ Y ∪ repl (fun z ↦ π₀ ‘ z) (by definability) C ; kpair.π₁ z = m₁})
      have hused : IsInternallyFinite used := by
        apply internallyFinite_repl
        apply internallyFinite_subset (internallyFinite_union hY (internallyFinite_repl _ _ hCfin))
        intro z hz
        exact (mem_sep_iff.mp hz).1
      obtain ⟨k', hk', hk'used⟩ := internallyFinite_fresh_natural (internallyFinite_insert hused k₁)
      have hk'k₁ : k' ≠ k₁ := fun he ↦ hk'used (mem_insert.mpr (Or.inl he))
      have hfresh : ⟨m₁, k'⟩ₖ ∉ Y ∪ repl (fun z ↦ π₀ ‘ z) (by definability) C := by
        intro hmem
        apply hk'used
        apply mem_insert.mpr (Or.inr _)
        exact (repl_spec _).mpr ⟨⟨m₁, k'⟩ₖ, mem_sep_iff.mpr ⟨hmem, by simp⟩, by simp⟩
      let τ := internalTransposition (columnCoordinates V) ⟨m₁, k₁⟩ₖ ⟨m₁, k'⟩ₖ
      have hτ : IsColumnPermutation τ := columnTransposition_isColumnPermutation hm₁ hk₁ hk'
      have ha : ⟨m₁, k₁⟩ₖ ∈ columnCoordinates V := kpair_mem_iff.mpr ⟨hm₁, hk₁⟩
      have hb : ⟨m₁, k'⟩ₖ ∈ columnCoordinates V := kpair_mem_iff.mpr ⟨hm₁, hk'⟩
      refine ⟨compose π₀ τ, hπ₀.comp hτ, ?_, ?_⟩
      · intro z hz hzn
        rw [value_compose_of_mem_function hπ₀.1.1 hτ.1.1 hz, hfix₀ z hz hzn]
        have hz1 : z ≠ ⟨m₁, k₁⟩ₖ := by
          intro he
          rw [he] at hzn
          simp only [kpair.π₁_kpair] at hzn
          exact hcn hzn
        have hz2 : z ≠ ⟨m₁, k'⟩ₖ := by
          intro he
          rw [he] at hzn
          simp only [kpair.π₁_kpair] at hzn
          exact hcn hzn
        exact internalTransposition_fixed hz hz1 hz2
      · intro z hz
        rcases mem_insert.mp hz with rfl | hzC
        · rw [value_compose_of_mem_function hπ₀.1.1 hτ.1.1 hc, hw', internalTransposition_left ha]
          exact fun hh ↦ hfresh (mem_union_iff.mpr (Or.inl hh))
        · have hzc : z ∈ columnCoordinates V := hCc z (mem_insert.mpr (Or.inr hzC))
          rw [value_compose_of_mem_function hπ₀.1.1 hτ.1.1 hzc]
          have hwz : π₀ ‘ z ∈ columnCoordinates V := hπ₀.value_mem hzc
          have hne1 : π₀ ‘ z ≠ ⟨m₁, k₁⟩ₖ := by
            intro he
            rw [← hw'] at he
            have hzc' : z = ⟨m₁, k⟩ₖ := injective_value_eq hπ₀.1.1 hπ₀.1.2.1 hzc hc he
            have hmv := hmove₀ z hzC
            rw [hzc'] at hmv
            exact hwY hmv
          have hne2 : π₀ ‘ z ≠ ⟨m₁, k'⟩ₖ := by
            intro he
            apply hfresh
            apply mem_union_iff.mpr (Or.inr _)
            exact (repl_spec _).mpr ⟨z, hzC, he.symm⟩
          rw [internalTransposition_fixed hwz hne1 hne2]
          exact hmove₀ z hzC

end ZFVP
