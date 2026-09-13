import ZFVP.SetTheory.InternalPermutations

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def transpositionValue (a b x : V) : V := by
  classical
  exact if x = a then b else if x = b then a else x

instance transpositionValue_definable : ℒₛₑₜ-function₃[V] transpositionValue := by
  have h : ℒₛₑₜ-relation₄[V] (fun y a b x ↦
      (x = a ∧ y = b) ∨ (x ≠ a ∧ x = b ∧ y = a) ∨ (x ≠ a ∧ x ≠ b ∧ y = x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = transpositionValue (v 1) (v 2) (v 3) ↔ _
  unfold transpositionValue
  split_ifs <;> simp_all

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transpositionValue_left (a b : V) : transpositionValue a b a = b := by simp [transpositionValue]

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transpositionValue_right (a b : V) : transpositionValue a b b = a := by
  classical
  by_cases he : b = a <;> simp [transpositionValue, he]

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transpositionValue_fixed {a b x : V} (ha : x ≠ a) (hb : x ≠ b) :
    transpositionValue a b x = x := by simp [transpositionValue, ha, hb]

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transpositionValue_involutive (a b x : V) :
    transpositionValue a b (transpositionValue a b x) = x := by
  classical
  by_cases ha : x = a
  · subst x
    rw [transpositionValue_left, transpositionValue_right]
  · by_cases hb : x = b
    · subst x
      rw [transpositionValue_right, transpositionValue_left]
    · rw [transpositionValue_fixed ha hb, transpositionValue_fixed ha hb]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transpositionValue_mem {I a b x : V} (ha : a ∈ I) (hb : b ∈ I) (hx : x ∈ I) :
    transpositionValue a b x ∈ I := by
  unfold transpositionValue
  split_ifs <;> assumption

noncomputable def internalTransposition (I a b : V) : V :=
  definableGraph I (transpositionValue a b) (by definability)

instance internalTransposition_definable : ℒₛₑₜ-function₃[V] internalTransposition := by
  have h : ℒₛₑₜ-relation₄[V] (fun π I a b ↦ ∀ z, z ∈ π ↔ ∃ x ∈ I, z = ⟨x, transpositionValue a b x⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalTransposition (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [internalTransposition, mem_definableGraph_iff]

theorem internalTransposition_value {I a b x : V} (hx : x ∈ I) :
    (internalTransposition I a b) ‘ x = transpositionValue a b x := value_definableGraph _ _ _ hx

theorem internalTransposition_permutation {I a b : V} (ha : a ∈ I) (hb : b ∈ I) :
    IsInternalPermutation I (internalTransposition I a b) := by
  have hf : internalTransposition I a b ∈ I ^ I :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hx ↦ transpositionValue_mem ha hb hx)
  have : IsFunction (internalTransposition I a b) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_⟩
  · intro x y z hx hy
    have he := (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
    rw [internalTransposition_value (mem_of_mem_functions hf hx).1,
      internalTransposition_value (mem_of_mem_functions hf hy).1] at he
    have hh := congrArg (transpositionValue a b) he
    simpa only [transpositionValue_involutive] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro x hx
    have hm := transpositionValue_mem ha hb hx
    have he : (internalTransposition I a b) ‘ (transpositionValue a b x) = x := by
      rw [internalTransposition_value hm, transpositionValue_involutive]
    exact he ▸ value_mem_range hf hm

theorem internalTransposition_left {I a b : V} (ha : a ∈ I) : (internalTransposition I a b) ‘ a = b := by
  rw [internalTransposition_value ha, transpositionValue_left]

theorem internalTransposition_right {I a b : V} (hb : b ∈ I) : (internalTransposition I a b) ‘ b = a := by
  rw [internalTransposition_value hb, transpositionValue_right]

theorem internalTransposition_fixed {I a b x : V} (hx : x ∈ I) (ha : x ≠ a) (hb : x ≠ b) :
    (internalTransposition I a b) ‘ x = x := by
  rw [internalTransposition_value hx, transpositionValue_fixed ha hb]

end ZFVP
