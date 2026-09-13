import ZFVP.SetTheory.InternalPermutations
import ZFVP.SetTheory.DefinableGraph

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def disjointSwapValue (A f x : V) : V := by
  classical
  exact if x ∈ A then f ‘ x else if x ∈ range f then (converseGraph f) ‘ x else x

instance disjointSwapValue_definable : ℒₛₑₜ-function₃[V] disjointSwapValue := by
  have h : ℒₛₑₜ-relation₄[V] (fun y A f x ↦
    (x ∈ A ∧ y = f ‘ x) ∨
    (x ∉ A ∧ x ∈ range f ∧ y = (converseGraph f) ‘ x) ∨
    (x ∉ A ∧ x ∉ range f ∧ y = x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = disjointSwapValue (v 1) (v 2) (v 3) ↔ _
  unfold disjointSwapValue
  split_ifs <;> simp_all

theorem disjointSwapValue_left {A f x : V} (hx : x ∈ A) :
    disjointSwapValue A f x = f ‘ x := by simp [disjointSwapValue, hx]

theorem disjointSwapValue_involutive {I A f : V} (hf : f ∈ I ^ A)
    (hinj : Injective f) (hdis : ∀ x ∈ range f, x ∉ A) (x : V) :
    disjointSwapValue A f (disjointSwapValue A f x) = x := by
  classical
  have hi := converseGraph_mem_function hf hinj
  by_cases hx : x ∈ A
  · have hr := value_mem_range hf hx
    rw [disjointSwapValue_left hx]
    simp only [disjointSwapValue, hdis _ hr, hr, ↓reduceIte]
    exact converseGraph_value_value hf hinj hx
  · by_cases hr : x ∈ range f
    · have hy := function_value_mem hi hr
      have he : disjointSwapValue A f x = (converseGraph f) ‘ x := by
        simp [disjointSwapValue, hx, hr]
      rw [he, disjointSwapValue_left hy]
      exact value_converseGraph_value hf hinj hr
    · simp [disjointSwapValue, hx, hr]

theorem disjointSwapValue_mem {I A f x : V} (hf : f ∈ I ^ A)
    (hinj : Injective f) (hA : A ⊆ I) (hx : x ∈ I) :
    disjointSwapValue A f x ∈ I := by
  unfold disjointSwapValue
  split_ifs with ha hr
  · exact function_value_mem hf ha
  · exact hA _ (function_value_mem (converseGraph_mem_function hf hinj) hr)
  · exact hx

noncomputable def disjointSwap (I A f : V) : V :=
  definableGraph I (disjointSwapValue A f) (by definability)

instance disjointSwap_definable : ℒₛₑₜ-function₃[V] disjointSwap := by
  have h : ℒₛₑₜ-relation₄[V] (fun π I A f ↦ ∀ z, z ∈ π ↔
    ∃ x ∈ I, z = ⟨x, disjointSwapValue A f x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = disjointSwap (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [disjointSwap, mem_definableGraph_iff]

theorem disjointSwap_value {I A f x : V} (hx : x ∈ I) :
    (disjointSwap I A f) ‘ x = disjointSwapValue A f x := value_definableGraph _ _ _ hx

theorem disjointSwap_permutation {I A f : V} (hf : f ∈ I ^ A)
    (hinj : Injective f) (hA : A ⊆ I) (hdis : ∀ x ∈ range f, x ∉ A) :
    IsInternalPermutation I (disjointSwap I A f) := by
  have hg : disjointSwap I A f ∈ I ^ I :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun _ hx ↦ disjointSwapValue_mem hf hinj hA hx)
  let := IsFunction.of_mem hg
  refine ⟨hg, ?_, ?_⟩
  · intro x y z hx hy
    have he := (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
    rw [disjointSwap_value (mem_of_mem_functions hg hx).1,
      disjointSwap_value (mem_of_mem_functions hg hy).1] at he
    have hh := congrArg (disjointSwapValue A f) he
    simpa only [disjointSwapValue_involutive hf hinj hdis] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hg)
    intro x hx
    have hm := disjointSwapValue_mem hf hinj hA hx
    have he : (disjointSwap I A f) ‘ (disjointSwapValue A f x) = x := by
      rw [disjointSwap_value hm, disjointSwapValue_involutive hf hinj hdis]
    exact he ▸ value_mem_range hg hm

theorem disjointSwap_rows {I A f : V} (hf : f ∈ I ^ A)
    (hinj : Injective f) (hrow : ∀ x ∈ A, kpair.π₂ (f ‘ x) = kpair.π₂ x) :
    ∀ x ∈ I, kpair.π₂ ((disjointSwap I A f) ‘ x) = kpair.π₂ x := by
  intro x hx
  rw [disjointSwap_value hx]
  unfold disjointSwapValue
  split_ifs with ha hr
  · exact hrow x ha
  · have h := hrow _ (function_value_mem (converseGraph_mem_function hf hinj) hr)
    rw [value_converseGraph_value hf hinj hr] at h
    exact h.symm
  · rfl

end ZFVP
