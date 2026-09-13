import ZFVP.SetTheory.CoherentForcingBounds
import ZFVP.SetTheory.CompositionLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsCoherentForcingBoundColumn (θ P R B C T ρ M i I : V) : Prop where
  bound : (∀ f, IsForcingDirectedFamily C T I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (ρ ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      M ‘ ⟨f, p⟩ₖ ∈ C ∧ (∀ a ∈ I, ⟨M ‘ ⟨f, p⟩ₖ, f ‘ a⟩ₖ ∈ T) ∧ (ρ ‘ i) ‘ (M ‘ ⟨f, p⟩ₖ) = p)
  commute : (∀ j ∈ θ, i ⊆ j → ∀ f, IsForcingDirectedFamily C T I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (ρ ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (ρ ‘ j) ‘ (M ‘ ⟨f, p⟩ₖ) = (B ‘ j) ‘ ⟨compose f (ρ ‘ j), p⟩ₖ)

theorem IsCoherentForcingBound.extend {θ P R π B C T ρ M i I : V}
    (h : IsCoherentForcingBound θ P R π B i I)
    (c : IsCoherentForcingBoundColumn θ P R B C T ρ M i I) (hi : i ∈ θ) :
    IsCoherentForcingBound (succ θ) (forcingFamilyNext θ P C) (forcingFamilyNext θ R T)
      (forcingMatrixNext θ π ρ (identity C)) (forcingFamilyNext θ B M) i I := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  constructor
  · intro j hj hij f hf p hp hb
    rcases mem_succ_iff.mp hj with rfl | hj
    · simp only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingMatrixNext_column hi] at hf hp hb ⊢
      exact c.bound f hf p hp hb
    · simp only [forcingFamilyNext_old hj, forcingFamilyNext_old hi, forcingMatrixNext_old hi' hj] at hf hp hb ⊢
      exact h.bound j hj hij f hf p hp hb
  · intro j hj k hk hij hjk f hf p hp hb
    rcases mem_succ_iff.mp hk with rfl | hk
    · rcases mem_succ_iff.mp hj with rfl | hj
      · simp only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingMatrixNext_column hi,
          forcingMatrixNext_diagonal] at hf hp hb ⊢
        rw [graph_compose_identity hf.1, identity_value (c.bound f hf p hp hb).1]
      · simp only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingFamilyNext_old hj,
          forcingMatrixNext_column hi, forcingMatrixNext_column hj] at hf hp hb ⊢
        exact c.commute j hj hij f hf p hp hb
    · have hjold : j ∈ θ := by
        rcases mem_succ_iff.mp hj with rfl | hj
        · exact (mem_irrefl k (hjk k hk)).elim
        · exact hj
      simp only [forcingFamilyNext_old hi, forcingFamilyNext_old hk, forcingFamilyNext_old hjold,
        forcingMatrixNext_old hi' hk, forcingMatrixNext_old hj hk] at hf hp hb ⊢
      exact h.commute j hjold k hk hij hjk f hf p hp hb

end ZFVP
