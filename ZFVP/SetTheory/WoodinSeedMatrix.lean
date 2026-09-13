import ZFVP.SetTheory.WoodinSeedRestriction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSeedMatrixValue (M C z : V) : V := by
  classical
  exact if kpair.π₁ z = ∅ then C ‘ (kpair.π₂ z)
    else M ‘ ⟨woodinRecursiveIndex (kpair.π₁ z), woodinRecursiveIndex (kpair.π₂ z)⟩ₖ

instance woodinSeedMatrixValue_definable : ℒₛₑₜ-function₃[V] woodinSeedMatrixValue := by
  have hd : ℒₛₑₜ-relation₄ (fun y M C z : V ↦
    (kpair.π₁ z = ∅ ∧ y = C ‘ (kpair.π₂ z)) ∨
    (kpair.π₁ z ≠ ∅ ∧ y = M ‘ ⟨woodinRecursiveIndex (kpair.π₁ z),
      woodinRecursiveIndex (kpair.π₂ z)⟩ₖ)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedMatrixValue (v 1) (v 2) (v 3) ↔ _
  classical
  by_cases hz : kpair.π₁ (v 3) = ∅ <;> simp [woodinSeedMatrixValue, hz]

noncomputable def woodinSeedMatrix (θ M C : V) : V :=
  definableGraph (woodinSourceIndex θ ×ˢ woodinSourceIndex θ)
    (woodinSeedMatrixValue M C) (by definability)

instance woodinSeedMatrix_isFunction (θ M C : V) : IsFunction (woodinSeedMatrix θ M C) := by
  unfold woodinSeedMatrix
  infer_instance

theorem woodinSeedMatrix_zero {θ M C j : V} [IsOrdinal θ] (hj : j ∈ woodinSourceIndex θ) :
    (woodinSeedMatrix θ M C) ‘ ⟨∅, j⟩ₖ = C ‘ j := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  rw [woodinSeedMatrix, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hz, hj⟩)]
  simp [woodinSeedMatrixValue]

theorem woodinSeedMatrix_positive {θ M C i j : V} [IsOrdinal θ]
    (hi : i ∈ woodinSourceIndex θ) (hj : j ∈ woodinSourceIndex θ) (hne : i ≠ ∅) :
    (woodinSeedMatrix θ M C) ‘ ⟨i, j⟩ₖ =
      M ‘ ⟨woodinRecursiveIndex i, woodinRecursiveIndex j⟩ₖ := by
  rw [woodinSeedMatrix, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  simp [woodinSeedMatrixValue, hne]

theorem woodinSeedMatrix_at_sourceIndex {θ M C i j : V} [IsOrdinal θ]
    (hi : i ∈ θ) (hj : j ∈ θ) :
    (woodinSeedMatrix θ M C) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = M ‘ ⟨i, j⟩ₖ := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rw [woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr hi)
    (woodinSourceIndex_mem_iff.mpr hj) (woodinSourceIndex_nonzero i),
    woodinRecursiveIndex_sourceIndex, woodinRecursiveIndex_sourceIndex]

noncomputable def woodinSeedProjectionColumn (θ Q : V) : V :=
  definableGraph (woodinSourceIndex θ) (fun j ↦ (Q ‘ j) ×ˢ ({∅} : V)) (by definability)

theorem woodinSeedProjectionColumn_value {θ Q j p : V}
    (hj : j ∈ woodinSourceIndex θ) (hp : p ∈ Q ‘ j) :
    ((woodinSeedProjectionColumn θ Q) ‘ j) ‘ p = ∅ := by
  rw [woodinSeedProjectionColumn, value_definableGraph _ _ _ hj]
  have hf : IsFunction ((Q ‘ j) ×ˢ ({∅} : V)) := by
    apply IsFunction.of_mem (show (Q ‘ j) ×ˢ ({∅} : V) ∈ ({∅} : V) ^ (Q ‘ j) from ?_)
    apply mem_function.intro
    · exact subset_refl _
    · intro x hx
      refine ⟨∅, kpair_mem_iff.mpr ⟨hx, by simp⟩, ?_⟩
      intro y hy
      exact mem_singleton_iff.mp (kpair_mem_iff.mp hy).2
  let := hf
  exact value_eq_of_kpair_mem (kpair_mem_iff.mpr ⟨hp, by simp⟩)

noncomputable def woodinSeedProjections (θ P π : V) : V :=
  woodinSeedMatrix θ π (woodinSeedProjectionColumn θ (woodinInsertSeed θ P {∅}))

theorem woodinInsertSeed_coherent {θ P π f : V} [IsOrdinal θ]
    (hf : ∀ i ∈ θ, f ‘ i ∈ P ‘ i) (hc : IsCoherentThread θ π f) :
    IsCoherentThread (woodinSourceIndex θ) (woodinSeedProjections θ P π)
      (woodinInsertSeed θ f ∅) := by
  intro j hj i hij hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hjn : j ≠ ∅ := by intro h; subst j; exact not_mem_empty hij
  have hrj : woodinRecursiveIndex j ∈ θ := (woodinRecursiveIndex_mem_iff hjn).mpr hj
  by_cases hin : i = ∅
  · subst i
    rw [woodinSeedProjections, woodinSeedMatrix_zero hj]
    rw [woodinSeedProjectionColumn_value hj, woodinInsertSeed_zero]
    rw [woodinInsertSeed_nonzero hj hjn, woodinInsertSeed_nonzero hj hjn]
    exact hf _ hrj
  · have hri : woodinRecursiveIndex i ∈ θ := (woodinRecursiveIndex_mem_iff hin).mpr hi
    have hrij : woodinRecursiveIndex i ∈ woodinRecursiveIndex j := by
      apply woodinSourceIndex_mem_iff.mp
      simpa only [woodinSourceIndex_recursiveIndex _ hin,
        woodinSourceIndex_recursiveIndex _ hjn] using hij
    rw [woodinSeedProjections, woodinSeedMatrix_positive hi hj hin,
      woodinInsertSeed_nonzero hi hin, woodinInsertSeed_nonzero hj hjn]
    exact hc _ hrj _ hrij hri

theorem woodinRemoveSeed_coherent {θ P π g : V} [IsOrdinal θ]
    (hc : IsCoherentThread (woodinSourceIndex θ) (woodinSeedProjections θ P π) g) :
    IsCoherentThread θ π (woodinRemoveSeed θ g) := by
  intro j hj i hij hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hh := hc (woodinSourceIndex j) (woodinSourceIndex_mem_iff.mpr hj)
    (woodinSourceIndex i) (woodinSourceIndex_mem_iff.mpr hij) (woodinSourceIndex_mem_iff.mpr hi)
  rw [woodinSeedProjections, woodinSeedMatrix_at_sourceIndex hi hj] at hh
  rw [woodinRemoveSeed_value hj, woodinRemoveSeed_value hi]
  exact hh

theorem woodinInsertSeed_mem_inverseLimit {θ P π U f : V} [IsOrdinal θ]
    (hf : f ∈ forcingInverseLimit θ P π U) (hU : (∅ : V) ∈ U) :
    woodinInsertSeed θ f ∅ ∈ forcingInverseLimit (woodinSourceIndex θ)
      (woodinInsertSeed θ P {∅}) (woodinSeedProjections θ P π) U := by
  obtain ⟨hfun, hm, hc⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨woodinInsertSeed_function hfun hU, ?_, woodinInsertSeed_coherent hm hc⟩
  intro i hi
  by_cases hz : i = ∅
  · subst i
    rw [woodinInsertSeed_zero, woodinInsertSeed_zero]
    simp
  · let := IsOrdinal.of_mem hi
    rw [woodinInsertSeed_nonzero hi hz, woodinInsertSeed_nonzero hi hz]
    exact hm _ ((woodinRecursiveIndex_mem_iff hz).mpr hi)

theorem woodinRemoveSeed_mem_inverseLimit {θ P π U g : V} [IsOrdinal θ]
    (hg : g ∈ forcingInverseLimit (woodinSourceIndex θ)
      (woodinInsertSeed θ P {∅}) (woodinSeedProjections θ P π) U) :
    woodinRemoveSeed θ g ∈ forcingInverseLimit θ P π U := by
  obtain ⟨hfun, hm, hc⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hg
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨woodinRemoveSeed_function hfun, ?_, woodinRemoveSeed_coherent hc⟩
  intro i hi
  let := IsOrdinal.of_mem hi
  have hh := hm (woodinSourceIndex i) (woodinSourceIndex_mem_iff.mpr hi)
  rw [woodinInsertSeed_at_sourceIndex hi] at hh
  rw [woodinRemoveSeed_value hi]
  exact hh

theorem woodinSeed_inverseLimit_zero {θ P π U g : V} [IsOrdinal θ]
    (hg : g ∈ forcingInverseLimit (woodinSourceIndex θ)
      (woodinInsertSeed θ P {∅}) (woodinSeedProjections θ P π) U) : g ‘ ∅ = ∅ := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hh := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hg).2.1 ∅ hz
  rw [woodinInsertSeed_zero] at hh
  exact mem_singleton_iff.mp hh

end ZFVP
