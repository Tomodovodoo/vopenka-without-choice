import ZFVP.SetTheory.ClassForcingTowerCodes
import ZFVP.SetTheory.ForcingBoundCodeExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingCodeSequence
variable (C : DefinableForcingCodeSequence V)

noncomputable def history (θ : V) : V := definableGraph θ C.code C.definable

noncomputable def codePrefix (θ : V) : V := forcingIterationCodeUnion θ (C.history θ)

instance history_definable : ℒₛₑₜ-function₁ C.history := by
  have := C.definable
  have h : ℒₛₑₜ-relation (fun H θ : V ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, C.code i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = C.history (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [history, mem_definableGraph_iff]

instance prefix_definable : ℒₛₑₜ-function₁ C.codePrefix := by
  unfold codePrefix
  apply Language.DefinableFunction₂.comp (F := forcingIterationCodeUnion) <;> definability

theorem history_value {θ i : V} (hi : i ∈ θ) : (C.history θ) ‘ i = C.code i :=
  value_definableGraph _ _ _ hi

theorem history_valid (θ : V) [IsOrdinal θ] : IsForcingIterationHistory θ (C.history θ) := by
  refine ⟨⟨?_, domain_definableGraph _ _ _⟩, ?_, ?_⟩
  · unfold history
    infer_instance
  · intro i hi
    rw [C.history_value hi]
    exact C.valid i (IsOrdinal.of_mem hi)
  · intro i hi j hj hij
    rw [C.history_value hi, C.history_value hj]
    exact C.coherence i j (IsOrdinal.of_mem hi) (IsOrdinal.of_mem hj) hij

theorem prefix_valid (θ : V) [IsOrdinal θ] : IsForcingIterationCode θ (C.codePrefix θ) :=
  (C.history_valid θ).union_code

theorem prefix_extends {θ i : V} (hi : i ∈ θ) : ForcingCodeExtends (C.code i) (C.codePrefix θ) := by
  have h := forcingIterationCodeUnion_extends (H := C.history θ) hi
  rw [C.history_value hi] at h
  exact h

theorem prefix_P {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodeP (C.codePrefix θ)) ‘ i = C.tower.P i := by
  have := IsOrdinal.of_mem hi
  exact ((C.valid i inferInstance).tableP.value_of_subset (C.prefix_valid θ).tableP
    (C.prefix_extends hi).subP (mem_succ_self i)).symm

theorem prefix_R {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodeR (C.codePrefix θ)) ‘ i = C.tower.R i := by
  have := IsOrdinal.of_mem hi
  exact ((C.valid i inferInstance).tableR.value_of_subset (C.prefix_valid θ).tableR
    (C.prefix_extends hi).subR (mem_succ_self i)).symm

theorem prefix_top {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodet (C.codePrefix θ)) ‘ i = C.tower.top i := by
  have := IsOrdinal.of_mem hi
  exact ((C.valid i inferInstance).tablet.value_of_subset (C.prefix_valid θ).tablet
    (C.prefix_extends hi).subt (mem_succ_self i)).symm

theorem prefix_projection {θ i j : V} [IsOrdinal θ] [IsOrdinal i]
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeπ (C.codePrefix θ)) ‘ ⟨i, j⟩ₖ = C.tower.projection i j := by
  have := IsOrdinal.of_mem hj
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  exact ((C.valid j inferInstance).tableπ.value_of_subset (C.prefix_valid θ).tableπ
    (C.prefix_extends hj).subπ (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

theorem prefix_section {θ i j : V} [IsOrdinal θ] [IsOrdinal i]
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeE (C.codePrefix θ)) ‘ ⟨i, j⟩ₖ = C.tower.sectionMap i j := by
  have := IsOrdinal.of_mem hj
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  exact ((C.valid j inferInstance).tableE.value_of_subset (C.prefix_valid θ).tableE
    (C.prefix_extends hj).subE (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

end DefinableForcingCodeSequence
end ZFVP

