import ZFVP.SetTheory.ForcingBoundCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCoherentForcingBound.extend_fixed {θ P R π B ρ M i I : V}
    (h : IsCoherentForcingBound θ P R π B i I)
    (c : IsCoherentForcingBoundColumn θ P R B (P ‘ θ) (R ‘ θ) ρ M i I)
    (hi : i ∈ θ) (hρ : ∀ j ∈ θ, ρ ‘ j = π ‘ ⟨j, θ⟩ₖ)
    (hdiag : π ‘ ⟨θ, θ⟩ₖ = identity (P ‘ θ)) :
    IsCoherentForcingBound (succ θ) P R π (forcingFamilyNext θ B M) i I := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  constructor
  · intro j hj hij f hf p hp hb
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new]
      have hh := c.bound
      rw [hρ i hi] at hh
      exact hh f hf p hp hb
    · rw [forcingFamilyNext_old hj]
      exact h.bound j hj hij f hf p hp hb
  · intro j hj k hk hij hjk f hf p hp hb
    rcases mem_succ_iff.mp hk with rfl | hk
    · rcases mem_succ_iff.mp hj with rfl | hj
      · rw [forcingFamilyNext_new, hdiag, graph_compose_identity hf.1]
        have hh := c.bound
        rw [hρ i hi] at hh
        exact identity_value (hh f hf p hp hb).1
      · rw [forcingFamilyNext_new, forcingFamilyNext_old hj]
        have hh := c.commute j hj hij
        rw [hρ i hi, hρ j hj] at hh
        exact hh f hf p hp hb
    · have hjold : j ∈ θ := by
        rcases mem_succ_iff.mp hj with rfl | hj
        · exact (mem_irrefl k (hjk k hk)).elim
        · exact hj
      rw [forcingFamilyNext_old hk, forcingFamilyNext_old hjold]
      exact h.commute j hjold k hk hij hjk f hf p hp hb

theorem IsSectionCompatibleForcingBound.extend_fixed {θ P R π E B ρ F M i I : V}
    (h : IsSectionCompatibleForcingBound θ P R π E B i I)
    (c : IsCoherentForcingBoundColumn θ P R B (P ‘ θ) (R ‘ θ) ρ M i I)
    (hc : IsSectionCompatibleBoundColumn θ P R π B F M i I)
    (hi : i ∈ θ) (hρ : ρ ‘ i = π ‘ ⟨i, θ⟩ₖ)
    (hF : ∀ j ∈ θ, F ‘ j = E ‘ ⟨j, θ⟩ₖ)
    (hdiag : E ‘ ⟨θ, θ⟩ₖ = identity (P ‘ θ)) :
    IsSectionCompatibleForcingBound (succ θ) P R π E (forcingFamilyNext θ B M) i I := by
  constructor
  intro j hj k hk hij hjk f hf p hp hb
  rcases mem_succ_iff.mp hk with rfl | hk
  · rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new, hdiag, graph_compose_identity hf.1]
      have hh := c.bound
      rw [hρ] at hh
      exact (identity_value (hh f hf p hp hb).1).symm
    · rw [forcingFamilyNext_new, forcingFamilyNext_old hj]
      have hh := hc.compatible j hj hij
      rw [hF j hj] at hh
      exact hh f hf p hp hb
  · have hjold : j ∈ θ := by
      rcases mem_succ_iff.mp hj with rfl | hj
      · exact (mem_irrefl k (hjk k hk)).elim
      · exact hj
    rw [forcingFamilyNext_old hk, forcingFamilyNext_old hjold]
    exact h.compatible j hjold k hk hij hjk f hf p hp hb

end ZFVP
