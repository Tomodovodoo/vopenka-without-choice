import ZFVP.SetTheory.ForcingLiftExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsSectionCompatibleForcingLift (θ P R π E L : V) : Prop where
  compatible : (∀ i ∈ θ, ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j →
    ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ i, ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
    (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ a, b⟩ₖ =
      (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ))

structure IsSectionCompatibleLiftColumn (θ P R π L F M : V) : Prop where
  compatible : (∀ i ∈ θ, ∀ k ∈ θ, i ⊆ k → ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ i,
    ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
    (M ‘ i) ‘ ⟨(F ‘ k) ‘ a, b⟩ₖ = (F ‘ k) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ))

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsSectionCompatibleForcingLift.extend {θ P R π E L Q T ρ F M : V}
    (h : IsSectionCompatibleForcingLift θ P R π E L)
    (c : IsCoherentForcingLiftColumn θ P R π L Q T ρ M)
    (s : IsSectionCompatibleLiftColumn θ P R π L F M) :
    IsSectionCompatibleForcingLift (succ θ) (forcingFamilyNext θ P Q) (forcingFamilyNext θ R T)
      (forcingMatrixNext θ π ρ (identity Q)) (forcingMatrixNext θ E F (identity Q))
      (forcingMatrixNext θ L M (forcingIdentityLift Q)) := by
  refine ⟨?_⟩
  intro i hi k hk j hj hik hkj a ha b hb hle
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases mem_succ_iff.mp hk with rfl | hk
    · rw [forcingFamilyNext_new] at ha
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hb
        rw [forcingMatrixNext_diagonal, forcingMatrixNext_diagonal,
          identity_value ha, forcingIdentityLift_value ha hb, identity_value hb]
      · rw [forcingFamilyNext_old hi] at hb
        rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi] at hle
        have hq := (c.lift i hi a ha b hb hle).1
        rw [forcingMatrixNext_column hi, forcingMatrixNext_diagonal,
          identity_value ha, identity_value hq]
    · have hi' := old_of_subset_old hi hk hik
      rw [forcingFamilyNext_old hk] at ha
      rw [forcingFamilyNext_old hi'] at hb
      rw [forcingMatrixNext_old hi hk, forcingFamilyNext_old hi'] at hle
      rw [forcingMatrixNext_column hi', forcingMatrixNext_column hk, forcingMatrixNext_old hi hk]
      exact s.compatible i hi' k hk hik a ha b hb hle
  · have hk' := old_of_subset_old hk hj hkj
    have hi' := old_of_subset_old hi hk' hik
    rw [forcingFamilyNext_old hk'] at ha
    rw [forcingFamilyNext_old hi'] at hb
    rw [forcingMatrixNext_old hi hk', forcingFamilyNext_old hi'] at hle
    rw [forcingMatrixNext_old hi hj, forcingMatrixNext_old hk hj, forcingMatrixNext_old hi hk']
    exact h.compatible i hi' k hk' j hj hik hkj a ha b hb hle

end ZFVP
