import ZFVP.SetTheory.ForcingSystemExtension
import ZFVP.SetTheory.ForcingLimitCodes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance forcingThreadCoordinate_parameter_definable (C : V) :
    ℒₛₑₜ-function₁[V] (forcingThreadCoordinate C) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ f ∈ C, z = ⟨f, f ‘ i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadCoordinate C (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadCoordinate, mem_definableGraph_iff]

instance forcingThreadSection_index_definable (θ P π E : V) :
    ℒₛₑₜ-function₁[V] (forcingThreadSection θ P π E) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ p ∈ P ‘ i,
    z = ⟨p, forcingSectionThread θ π E i p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadSection θ P π E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadSection, mem_definableGraph_iff]

noncomputable def forcingLimitProjectionColumn (θ C : V) : V :=
  definableGraph θ (forcingThreadCoordinate C) (forcingThreadCoordinate_parameter_definable C)

noncomputable def forcingLimitSectionColumn (θ P π E : V) : V :=
  definableGraph θ (forcingThreadSection θ P π E) (forcingThreadSection_index_definable θ P π E)

theorem forcingLimitProjectionColumn_value {θ C i : V} (hi : i ∈ θ) :
    (forcingLimitProjectionColumn θ C) ‘ i = forcingThreadCoordinate C i :=
  value_definableGraph _ _ _ hi

theorem forcingLimitSectionColumn_value {θ P π E i : V} (hi : i ∈ θ) :
    (forcingLimitSectionColumn θ P π E) ‘ i = forcingThreadSection θ P π E i :=
  value_definableGraph _ _ _ hi

/-- Any carrier between the direct and inverse limits has the canonical split columns. -/
theorem forcingLimit_splitColumn {θ P π E U C : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) (hI : C ⊆ forcingInverseLimit θ P π U) :
    IsSplitForcingColumn θ P π E C
      (forcingLimitProjectionColumn θ C) (forcingLimitSectionColumn θ P π E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi f hf
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hf]
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hI f hf)).2.1 i hi
  · intro i hi p hp
    rw [forcingLimitSectionColumn_value hi, forcingThreadSection_value hp]
    exact hD _ (forcingSectionThread_mem h hi hp hU)
  · intro i hi j hj hij f hf
    rw [forcingLimitProjectionColumn_value hi, forcingLimitProjectionColumn_value hj,
      forcingThreadCoordinate_value hf, forcingThreadCoordinate_value hf]
    exact forcingInverseLimit_project_subset h (hI f hf) hi hj hij
  · intro i hi j hj hij p hp
    rw [forcingLimitSectionColumn_value hi, forcingLimitSectionColumn_value hj,
      forcingThreadSection_value hp, forcingThreadSection_value (h.secMaps i hi j hj hij p hp)]
    exact forcingSectionThread_comp h hi hj hij hp hU
  · intro i hi p hp
    rw [forcingLimitProjectionColumn_value hi, forcingLimitSectionColumn_value hi,
      forcingThreadSection_value hp,
      forcingThreadCoordinate_value (hD _ (forcingSectionThread_mem h hi hp hU)),
      forcingSectionThread_value hi, forcingSectionValue_self h hi hp]

end ZFVP
