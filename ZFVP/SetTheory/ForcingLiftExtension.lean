import ZFVP.SetTheory.ForcingSystemExtension
import ZFVP.SetTheory.ForcingThreadSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingIdentityLift (Q : V) : V :=
  definableGraph (Q ×ˢ Q) kpair.π₂ (by definability)

theorem forcingIdentityLift_value {Q a b : V} (ha : a ∈ Q) (hb : b ∈ Q) :
    (forcingIdentityLift Q) ‘ ⟨a, b⟩ₖ = b := by
  rw [forcingIdentityLift, value_definableGraph _ _ _ (mem_prod_iff.mpr ⟨a, ha, b, hb, rfl⟩),
    kpair.π₂_kpair]

structure IsCoherentForcingLiftColumn (θ P R π L Q T ρ M : V) : Prop where
  lift : (∀ i ∈ θ, ∀ a ∈ Q, ∀ b ∈ P ‘ i, ⟨b, (ρ ‘ i) ‘ a⟩ₖ ∈ R ‘ i →
    (M ‘ i) ‘ ⟨a, b⟩ₖ ∈ Q ∧ ⟨(M ‘ i) ‘ ⟨a, b⟩ₖ, a⟩ₖ ∈ T ∧
    (ρ ‘ i) ‘ ((M ‘ i) ‘ ⟨a, b⟩ₖ) = b)
  commute : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ Q, ∀ b ∈ P ‘ i,
    ⟨b, (ρ ‘ i) ‘ a⟩ₖ ∈ R ‘ i →
    (ρ ‘ j) ‘ ((M ‘ i) ‘ ⟨a, b⟩ₖ) = (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(ρ ‘ j) ‘ a, b⟩ₖ)

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsCoherentForcingLift.extend {θ P R π L Q T ρ M : V}
    (h : IsCoherentForcingLift θ P R π L)
    (c : IsCoherentForcingLiftColumn θ P R π L Q T ρ M) :
    IsCoherentForcingLift (succ θ) (forcingFamilyNext θ P Q) (forcingFamilyNext θ R T)
      (forcingMatrixNext θ π ρ (identity Q)) (forcingMatrixNext θ L M (forcingIdentityLift Q)) := by
  have lift : ∀ i ∈ succ θ, ∀ j ∈ succ θ, i ⊆ j →
      ∀ a ∈ (forcingFamilyNext θ P Q) ‘ j, ∀ b ∈ (forcingFamilyNext θ P Q) ‘ i,
      ⟨b, ((forcingMatrixNext θ π ρ (identity Q)) ‘ ⟨i, j⟩ₖ) ‘ a⟩ₖ ∈
        (forcingFamilyNext θ R T) ‘ i →
      ((forcingMatrixNext θ L M (forcingIdentityLift Q)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ ∈
        (forcingFamilyNext θ P Q) ‘ j ∧
      ⟨((forcingMatrixNext θ L M (forcingIdentityLift Q)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ, a⟩ₖ ∈
        (forcingFamilyNext θ R T) ‘ j ∧
      ((forcingMatrixNext θ π ρ (identity Q)) ‘ ⟨i, j⟩ₖ) ‘
        (((forcingMatrixNext θ L M (forcingIdentityLift Q)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) = b := by
    intro i hi j hj hij a ha b hb hle
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new] at ha
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hb
        rw [forcingMatrixNext_diagonal, forcingFamilyNext_new, identity_value ha] at hle
        rw [forcingMatrixNext_diagonal, forcingMatrixNext_diagonal,
          forcingFamilyNext_new, forcingFamilyNext_new, forcingIdentityLift_value ha hb,
          identity_value hb]
        exact ⟨hb, hle, rfl⟩
      · rw [forcingFamilyNext_old hi] at hb
        rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi] at hle
        rw [forcingMatrixNext_column hi, forcingMatrixNext_column hi,
          forcingFamilyNext_new, forcingFamilyNext_new]
        exact c.lift i hi a ha b hb hle
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hj] at ha
      rw [forcingFamilyNext_old hi'] at hb
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi'] at hle
      rw [forcingMatrixNext_old hi hj, forcingMatrixNext_old hi hj,
        forcingFamilyNext_old hj, forcingFamilyNext_old hj]
      exact h.lift i hi' j hj hij a ha b hb hle
  refine ⟨lift, ?_⟩
  intro i hi j hj k hk hij hjk a ha b hb hle
  rcases mem_succ_iff.mp hk with rfl | hk
  · have hq := (lift i hi _ (mem_succ_iff.mpr (Or.inl rfl))
      (fun x hx ↦ hjk x (hij x hx)) a ha b hb hle).1
    rw [forcingFamilyNext_new] at ha hq
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingMatrixNext_diagonal, identity_value hq, identity_value ha]
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hi'] at hb
      rw [forcingMatrixNext_column hi', forcingFamilyNext_old hi'] at hle
      rw [forcingMatrixNext_column hj, forcingMatrixNext_column hi',
        forcingMatrixNext_old hi hj]
      exact c.commute i hi' j hj hij a ha b hb hle
  · have hj' := old_of_subset_old hj hk hjk
    have hi' := old_of_subset_old hi hj' hij
    rw [forcingFamilyNext_old hk] at ha
    rw [forcingFamilyNext_old hi'] at hb
    rw [forcingMatrixNext_old hi hk, forcingFamilyNext_old hi'] at hle
    rw [forcingMatrixNext_old hj hk, forcingMatrixNext_old hi hk, forcingMatrixNext_old hi hj']
    exact h.commute i hi' j hj' k hk hij hjk a ha b hb hle

end ZFVP

