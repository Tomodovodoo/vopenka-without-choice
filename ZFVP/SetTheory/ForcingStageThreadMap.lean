import ZFVP.SetTheory.ForcingStageConditions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingStageThread_definable (θ π E : V) :
    ℒₛₑₜ-function₁[V] (fun z ↦ forcingSectionThread θ π E (kpair.π₁ z) (kpair.π₂ z)) := by
  classical
  have h : ℒₛₑₜ-relation (fun f z : V ↦ ∀ w, w ∈ f ↔ ∃ i ∈ θ,
    (i ∈ kpair.π₁ z ∧ w = ⟨i, (π ‘ ⟨i, kpair.π₁ z⟩ₖ) ‘ (kpair.π₂ z)⟩ₖ) ∨
    (i ∉ kpair.π₁ z ∧ w = ⟨i, (E ‘ ⟨kpair.π₁ z, i⟩ₖ) ‘ (kpair.π₂ z)⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSectionThread θ π E (kpair.π₁ (v 1)) (kpair.π₂ (v 1)) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro w
  rw [forcingSectionThread, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro i
  by_cases hi : i ∈ kpair.π₁ (v 1) <;> simp [forcingSectionValue, hi]

noncomputable def forcingStageThreadMap (θ P π E U : V) : V :=
  definableGraph (forcingStageConditions θ P U)
    (fun z ↦ forcingSectionThread θ π E (kpair.π₁ z) (kpair.π₂ z))
    (forcingStageThread_definable θ π E)

theorem forcingStageThreadMap_value {θ P π E U z : V}
    (hz : z ∈ forcingStageConditions θ P U) :
    (forcingStageThreadMap θ P π E U) ‘ z =
      forcingSectionThread θ π E (kpair.π₁ z) (kpair.π₂ z) :=
  value_definableGraph _ _ _ hz

theorem forcingStageThreadMap_maps {θ P π E U : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    forcingStageThreadMap θ P π E U ∈
      forcingDirectLimit θ P π E U ^ forcingStageConditions θ P U := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  exact (mem_forcingDirectLimit_iff_stage_condition h hU).mpr ⟨z, hz, rfl⟩

theorem forcingStageThreadMap_surjective {θ P π E U f : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hf : f ∈ forcingDirectLimit θ P π E U) :
    ∃ z ∈ forcingStageConditions θ P U, (forcingStageThreadMap θ P π E U) ‘ z = f := by
  obtain ⟨z, hz, he⟩ := (mem_forcingDirectLimit_iff_stage_condition h hU).mp hf
  exact ⟨z, hz, (forcingStageThreadMap_value hz).trans he.symm⟩

end ZFVP
