import ZFVP.SetTheory.ForcingLimitLift
import ZFVP.SetTheory.ForcingLimitColumns
import ZFVP.SetTheory.ForcingLiftExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingThreadSplice_index_parameters_definable (θ π L : V) :
    ℒₛₑₜ-function₃[V] (forcingThreadSplice θ π L) := by
  classical
  have h : ℒₛₑₜ-relation₄ (fun g f i b : V ↦ ∀ z, z ∈ g ↔ ∃ j ∈ θ,
    (j ∈ i ∧ z = ⟨j, (π ‘ ⟨j, i⟩ₖ) ‘ b⟩ₖ) ∨
    (j ∉ i ∧ z = ⟨j, (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadSplice θ π L (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingThreadSplice, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro j
  by_cases hj : j ∈ v 2 <;> simp [forcingSpliceValue, hj]

instance forcingLimitLift_index_definable (C θ P π L : V) :
    ℒₛₑₜ-function₁[V] (fun i ↦ forcingLimitLift C (P ‘ i) θ π L i) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ a ∈ C ×ˢ (P ‘ i),
    z = ⟨a, forcingThreadSplice θ π L (kpair.π₁ a) i (kpair.π₂ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingLimitLift C (P ‘ (v 1)) θ π L (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLimitLift, mem_definableGraph_iff]

noncomputable def forcingLimitLiftColumn (C θ P π L : V) : V :=
  definableGraph θ (fun i ↦ forcingLimitLift C (P ‘ i) θ π L i)
    (forcingLimitLift_index_definable C θ P π L)

theorem forcingLimitLiftColumn_value {C θ P π L i : V} (hi : i ∈ θ) :
    (forcingLimitLiftColumn C θ P π L) ‘ i = forcingLimitLift C (P ‘ i) θ π L i :=
  value_definableGraph _ _ _ hi

theorem forcingLimit_coherentLiftColumn {θ P R π E L U C : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hI : C ⊆ forcingInverseLimit θ P π U) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hπ : ∀ i ∈ θ, ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j)
    (hC : ∀ f ∈ C, ∀ i ∈ θ, ∀ b ∈ P ‘ i, ⟨b, f ‘ i⟩ₖ ∈ R ‘ i →
      forcingThreadSplice θ π L f i b ∈ C) :
    IsCoherentForcingLiftColumn θ P R π L C (forcingThreadOrder θ R C)
      (forcingLimitProjectionColumn θ C) (forcingLimitLiftColumn C θ P π L) := by
  refine ⟨?_, ?_⟩
  · intro i hi f hf b hb hle
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hf] at hle
    have hg := hC f hf i hi b hb hle
    have hle' := forcingThreadSplice_le h hL (hI f hf) hi hb hle hU (hπ i hi)
    rw [forcingLimitLiftColumn_value hi, forcingLimitLift_value hf hb,
      forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hg]
    exact ⟨hg, (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
      ⟨hg, hf, ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hle').2.2⟩,
      (forcingThreadSplice_value hi).trans (forcingSpliceValue_self h hL (hI f hf) hi hb hle)⟩
  · intro i hi j hj hij f hf b hb hle
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hf] at hle
    have hg := hC f hf i hi b hb hle
    rw [forcingLimitLiftColumn_value hi, forcingLimitLift_value hf hb,
      forcingLimitProjectionColumn_value hj, forcingThreadCoordinate_value hg,
      forcingThreadCoordinate_value hf]
    exact forcingThreadSplice_coordinate hj hij

theorem forcingInverseLimit_coherentLiftColumn {θ P R π E L U : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hπ : ∀ i ∈ θ, ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j) :
    IsCoherentForcingLiftColumn θ P R π L (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingLimitProjectionColumn θ (forcingInverseLimit θ P π U))
      (forcingLimitLiftColumn (forcingInverseLimit θ P π U) θ P π L) :=
  forcingLimit_coherentLiftColumn h hL (fun _ hf ↦ hf) hU hπ
    (fun _ hf _ hi _ hb hle ↦ forcingThreadSplice_mem h hL hf hi hb hle hU)

theorem forcingDirectLimit_coherentLiftColumn {θ P R π E L U : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hπ : ∀ i ∈ θ, ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j)
    (hcompat : ∀ i ∈ θ, ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j →
      ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ i, ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ a, b⟩ₖ =
        (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ)) :
    IsCoherentForcingLiftColumn θ P R π L (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingLimitProjectionColumn θ (forcingDirectLimit θ P π E U))
      (forcingLimitLiftColumn (forcingDirectLimit θ P π E U) θ P π L) :=
  forcingLimit_coherentLiftColumn h hL (forcingDirectLimit_subset _ _ _ _ _) hU hπ
    (fun _ hf _ hi _ hb hle ↦ forcingThreadSplice_direct_mem h hL hf hi hb hle hU (hcompat _ hi))

end ZFVP
