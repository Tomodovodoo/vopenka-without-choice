import ZFVP.SetTheory.ForcingSystemExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsToppedSplitForcingSystem (θ P R π E t : V) : Prop where
  top : (∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
  projTop : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (π ‘ ⟨i, j⟩ₖ) ‘ (t ‘ j) = t ‘ i)
  secTop : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ‘ (t ‘ i) = t ‘ j)

structure IsToppedSplitForcingColumn (θ t Q T ρ F u : V) : Prop where
  top : IsForcingTop Q T u
  projTop : (∀ i ∈ θ, (ρ ‘ i) ‘ u = t ‘ i)
  secTop : (∀ i ∈ θ, (F ‘ i) ‘ (t ‘ i) = u)

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsToppedSplitForcingSystem.extend {θ P R π E t Q T ρ F u : V}
    (h : IsToppedSplitForcingSystem θ P R π E t)
    (c : IsToppedSplitForcingColumn θ t Q T ρ F u) :
    IsToppedSplitForcingSystem (succ θ) (forcingFamilyNext θ P Q)
      (forcingFamilyNext θ R T) (forcingMatrixNext θ π ρ (identity Q))
      (forcingMatrixNext θ E F (identity Q)) (forcingFamilyNext θ t u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · simpa only [forcingFamilyNext_new] using c.top
    · simpa only [forcingFamilyNext_old hi] using h.top i hi
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new]
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingMatrixNext_diagonal, forcingFamilyNext_new, identity_value c.top.1]
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi]
        exact c.projTop i hi
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hj, forcingFamilyNext_old hi']
      exact h.projTop i hi' j hj hij
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingMatrixNext_diagonal, forcingFamilyNext_new, identity_value c.top.1]
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi, forcingFamilyNext_new]
        exact c.secTop i hi
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi', forcingFamilyNext_old hj]
      exact h.secTop i hi' j hj hij

end ZFVP
