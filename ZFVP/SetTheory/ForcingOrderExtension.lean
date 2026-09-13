import ZFVP.SetTheory.ForcingSystemExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Order laws for the coded projections and sections of an iteration. -/
structure IsOrderedSplitForcingSystem (θ P R π E : V) : Prop where
  preorder : (∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
  projMono : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ P ‘ j, ∀ b ∈ P ‘ j,
    ⟨a, b⟩ₖ ∈ R ‘ j → ⟨(π ‘ ⟨i, j⟩ₖ) ‘ a, (π ‘ ⟨i, j⟩ₖ) ‘ b⟩ₖ ∈ R ‘ i)
  below : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ P ‘ j, ∀ b ∈ P ‘ i,
    ⟨a, (E ‘ ⟨i, j⟩ₖ) ‘ b⟩ₖ ∈ R ‘ j ↔ ⟨(π ‘ ⟨i, j⟩ₖ) ‘ a, b⟩ₖ ∈ R ‘ i)

structure IsOrderedSplitForcingColumn (θ P R Q T ρ F : V) : Prop where
  preorder : IsForcingPreorder Q T
  projMono : (∀ i ∈ θ, ∀ a ∈ Q, ∀ b ∈ Q, ⟨a, b⟩ₖ ∈ T →
    ⟨(ρ ‘ i) ‘ a, (ρ ‘ i) ‘ b⟩ₖ ∈ R ‘ i)
  below : (∀ i ∈ θ, ∀ a ∈ Q, ∀ b ∈ P ‘ i,
    ⟨a, (F ‘ i) ‘ b⟩ₖ ∈ T ↔ ⟨(ρ ‘ i) ‘ a, b⟩ₖ ∈ R ‘ i)

theorem IsOrderedSplitForcingSystem.secMono {θ P R π E i j a b : V}
    (h : IsOrderedSplitForcingSystem θ P R π E) (s : IsSplitForcingSystem θ P π E)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (ha : a ∈ P ‘ i) (hb : b ∈ P ‘ i) (hab : ⟨a, b⟩ₖ ∈ R ‘ i) :
    ⟨(E ‘ ⟨i, j⟩ₖ) ‘ a, (E ‘ ⟨i, j⟩ₖ) ‘ b⟩ₖ ∈ R ‘ j := by
  apply (h.below i hi j hj hij _ (s.secMaps i hi j hj hij a ha) b hb).mpr
  rwa [s.retraction i hi j hj hij a ha]

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsOrderedSplitForcingSystem.extend {θ P R π E Q T ρ F : V}
    (h : IsOrderedSplitForcingSystem θ P R π E)
    (c : IsOrderedSplitForcingColumn θ P R Q T ρ F) :
    IsOrderedSplitForcingSystem (succ θ) (forcingFamilyNext θ P Q)
      (forcingFamilyNext θ R T) (forcingMatrixNext θ π ρ (identity Q))
      (forcingMatrixNext θ E F (identity Q)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · simpa only [forcingFamilyNext_new] using c.preorder
    · simpa only [forcingFamilyNext_old hi] using h.preorder i hi
  · intro i hi j hj hij a ha b hb hab
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new] at ha hb hab
      rcases mem_succ_iff.mp hi with rfl | hi
      · rwa [forcingMatrixNext_diagonal, forcingFamilyNext_new,
          identity_value ha, identity_value hb]
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi]
        exact c.projMono i hi a ha b hb hab
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hj] at ha hb hab
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi']
      exact h.projMono i hi' j hj hij a ha b hb hab
  · intro i hi j hj hij a ha b hb
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new] at ha
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hb
        rw [forcingMatrixNext_diagonal, forcingMatrixNext_diagonal,
          forcingFamilyNext_new, identity_value ha, identity_value hb]
      · rw [forcingFamilyNext_old hi] at hb
        rw [forcingMatrixNext_column hi, forcingMatrixNext_column hi,
          forcingFamilyNext_new, forcingFamilyNext_old hi]
        exact c.below i hi a ha b hb
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hj] at ha
      rw [forcingFamilyNext_old hi'] at hb
      rw [forcingMatrixNext_old hi hj, forcingMatrixNext_old hi hj,
        forcingFamilyNext_old hj, forcingFamilyNext_old hi']
      exact h.below i hi' j hj hij a ha b hb

end ZFVP
