import ZFVP.SetTheory.ForcingSystemExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsFunctionalSplitForcingSystem (θ P π E : V) : Prop where
  projection : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (π ‘ ⟨i, j⟩ₖ) ∈ (P ‘ i) ^ (P ‘ j))
  sectionMap : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ∈ (P ‘ j) ^ (P ‘ i))

structure IsFunctionalSplitForcingColumn (θ P Q ρ F : V) : Prop where
  projection : (∀ i ∈ θ, ρ ‘ i ∈ (P ‘ i) ^ Q)
  sectionMap : (∀ i ∈ θ, F ‘ i ∈ Q ^ (P ‘ i))

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsFunctionalSplitForcingSystem.extend {θ P π E Q ρ F : V}
    (h : IsFunctionalSplitForcingSystem θ P π E)
    (c : IsFunctionalSplitForcingColumn θ P Q ρ F) :
    IsFunctionalSplitForcingSystem (succ θ) (forcingFamilyNext θ P Q)
      (forcingMatrixNext θ π ρ (identity Q)) (forcingMatrixNext θ E F (identity Q)) := by
  constructor
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingMatrixNext_diagonal, forcingFamilyNext_new]
        exact identity_mem_function Q
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_new, forcingFamilyNext_old hi]
        exact c.projection i hi
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi', forcingFamilyNext_old hj]
      exact h.projection i hi' j hj hij
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingMatrixNext_diagonal, forcingFamilyNext_new]
        exact identity_mem_function Q
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_new, forcingFamilyNext_old hi]
        exact c.sectionMap i hi
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi', forcingFamilyNext_old hj]
      exact h.sectionMap i hi' j hj hij

end ZFVP
