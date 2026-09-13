import ZFVP.SetTheory.ForcingIterationTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def iterationTableUnion (I : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) : V := ⋃ˢ (repl F hF I)

theorem iterationTableUnion_compatible {I : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hf : ∀ i ∈ I, IsFunction (F i))
    (hd : ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, F i ⊆ F k ∧ F j ⊆ F k) :
    CompatibleFunctionFamily (repl F hF I) := by
  apply compatibleFunctionFamily_of_directed
  · intro f hf'
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hf'
    exact hf i hi
  · intro f hf' g hg'
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hf'
    obtain ⟨j, hj, rfl⟩ := (repl_spec hF).mp hg'
    obtain ⟨k, hk, hik, hjk⟩ := hd i hi j hj
    exact ⟨F k, (repl_spec hF).mpr ⟨k, hk, rfl⟩, hik, hjk⟩

theorem iterationTableUnion_table {I A : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hf : ∀ i ∈ I, IsFunction (F i))
    (hd : ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, F i ⊆ F k ∧ F j ⊆ F k)
    (hA : ∀ x, x ∈ A ↔ ∃ i ∈ I, x ∈ domain (F i)) :
    IsIterationTable A (iterationTableUnion I F hF) := by
  apply IsIterationTable.sUnion
  · intro f hf'
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hf'
    exact hf i hi
  · exact iterationTableUnion_compatible hF hf hd
  · intro x
    rw [hA x]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨F i, (repl_spec hF).mpr ⟨i, hi, rfl⟩, hx⟩
    · rintro ⟨f, hf', hx⟩
      obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hf'
      exact ⟨i, hi, hx⟩

theorem iterationTableUnion_restrict {I A i : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hf : ∀ j ∈ I, IsFunction (F j))
    (hd : ∀ j ∈ I, ∀ k ∈ I, ∃ l ∈ I, F j ⊆ F l ∧ F k ⊆ F l)
    (hi : i ∈ I) (ht : IsIterationTable A (F i)) :
    (iterationTableUnion I F hF) ↾ A = F i := by
  apply ht.restrict_union
  · intro f hf'
    obtain ⟨j, hj, rfl⟩ := (repl_spec hF).mp hf'
    exact hf j hj
  · exact iterationTableUnion_compatible hF hf hd
  · exact (repl_spec hF).mpr ⟨i, hi, rfl⟩

theorem iterationTableUnion_value {I i x : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hf : ∀ j ∈ I, IsFunction (F j))
    (hd : ∀ j ∈ I, ∀ k ∈ I, ∃ l ∈ I, F j ⊆ F l ∧ F k ⊆ F l)
    (hi : i ∈ I) (hx : x ∈ domain (F i)) :
    (iterationTableUnion I F hF) ‘ x = (F i) ‘ x := by
  apply value_sUnion_of_mem
  · intro f hf'
    obtain ⟨j, hj, rfl⟩ := (repl_spec hF).mp hf'
    exact hf j hj
  · exact iterationTableUnion_compatible hF hf hd
  · exact (repl_spec hF).mpr ⟨i, hi, rfl⟩
  · exact hx

theorem ordinal_prefix_domain {θ : V} [IsOrdinal θ] (x : V) :
    x ∈ θ ↔ ∃ i ∈ θ, x ∈ succ i := by
  constructor
  · intro hx
    exact ⟨x, hx, mem_succ_iff.mpr (Or.inl rfl)⟩
  · rintro ⟨i, hi, hx⟩
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hi
    · exact IsOrdinal.toIsTransitive.mem_trans hx hi

theorem ordinal_matrix_prefix_domain {θ : V} [IsOrdinal θ] (z : V) :
    z ∈ θ ×ˢ θ ↔ ∃ i ∈ θ, z ∈ succ i ×ˢ succ i := by
  constructor
  · intro hz
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_prod_iff.mp hz
    have : IsOrdinal j := IsOrdinal.of_mem hj
    have : IsOrdinal k := IsOrdinal.of_mem hk
    have self (i : V) : i ∈ succ i := mem_succ_iff.mpr (Or.inl rfl)
    rcases IsOrdinal.mem_trichotomy j k with hjk | rfl | hkj
    · exact ⟨k, hk, kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hjk), self k⟩⟩
    · exact ⟨j, hj, kpair_mem_iff.mpr ⟨self j, self j⟩⟩
    · exact ⟨j, hj, kpair_mem_iff.mpr ⟨self j, mem_succ_iff.mpr (Or.inr hkj)⟩⟩
  · rintro ⟨i, hi, hz⟩
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_prod_iff.mp hz
    exact kpair_mem_iff.mpr ⟨(ordinal_prefix_domain j).mpr ⟨i, hi, hj⟩,
      (ordinal_prefix_domain k).mpr ⟨i, hi, hk⟩⟩

theorem iterationTableUnion_family {θ : V} [IsOrdinal θ] {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hf : ∀ i ∈ θ, IsIterationTable (succ i) (F i))
    (hd : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, F i ⊆ F k ∧ F j ⊆ F k) :
    IsIterationTable θ (iterationTableUnion θ F hF) := by
  apply iterationTableUnion_table hF (fun i hi ↦ (hf i hi).function) hd
  intro x
  rw [ordinal_prefix_domain x]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, (hf i hi).domain_eq.symm ▸ hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, (hf i hi).domain_eq ▸ hx⟩

theorem iterationTableUnion_matrix {θ : V} [IsOrdinal θ] {F : V → V}
    (hF : ℒₛₑₜ-function₁ F)
    (hf : ∀ i ∈ θ, IsIterationTable (succ i ×ˢ succ i) (F i))
    (hd : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, F i ⊆ F k ∧ F j ⊆ F k) :
    IsIterationTable (θ ×ˢ θ) (iterationTableUnion θ F hF) := by
  apply iterationTableUnion_table hF (fun i hi ↦ (hf i hi).function) hd
  intro z
  rw [ordinal_matrix_prefix_domain z]
  constructor
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, hi, (hf i hi).domain_eq.symm ▸ hz⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, hi, (hf i hi).domain_eq ▸ hz⟩

end ZFVP
