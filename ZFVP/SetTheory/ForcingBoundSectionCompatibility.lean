import ZFVP.SetTheory.ForcingBoundInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsSectionCompatibleForcingBound (θ P R π E B i I : V) : Prop where
  compatible : (∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ f, IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (B ‘ k) ‘ ⟨compose f (E ‘ ⟨j, k⟩ₖ), p⟩ₖ = (E ‘ ⟨j, k⟩ₖ) ‘ ((B ‘ j) ‘ ⟨f, p⟩ₖ))

structure IsSectionCompatibleBoundColumn (θ P R π B F M i I : V) : Prop where
  compatible : (∀ j ∈ θ, i ⊆ j → ∀ f, IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f →
    ∀ p ∈ P ‘ i, (∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      M ‘ ⟨compose f (F ‘ j), p⟩ₖ = (F ‘ j) ‘ ((B ‘ j) ‘ ⟨f, p⟩ₖ))

theorem IsSectionCompatibleForcingBound.extend {θ P R π E B C T ρ F M i I : V}
    (h : IsSectionCompatibleForcingBound θ P R π E B i I)
    (c : IsCoherentForcingBoundColumn θ P R B C T ρ M i I)
    (hc : IsSectionCompatibleBoundColumn θ P R π B F M i I) (hi : i ∈ θ) :
    IsSectionCompatibleForcingBound (succ θ) (forcingFamilyNext θ P C) (forcingFamilyNext θ R T)
      (forcingMatrixNext θ π ρ (identity C)) (forcingMatrixNext θ E F (identity C))
      (forcingFamilyNext θ B M) i I := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  constructor
  intro j hj k hk hij hjk f hf p hp hb
  rcases mem_succ_iff.mp hk with rfl | hk
  · rcases mem_succ_iff.mp hj with rfl | hj
    · simp only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingMatrixNext_column hi,
        forcingMatrixNext_diagonal] at hf hp hb ⊢
      rw [graph_compose_identity hf.1, identity_value (c.bound f hf p hp hb).1]
    · simp only [forcingFamilyNext_new, forcingFamilyNext_old hi, forcingFamilyNext_old hj,
        forcingMatrixNext_old hi' hj, forcingMatrixNext_column hj] at hf hp hb ⊢
      exact hc.compatible j hj hij f hf p hp hb
  · have hjold : j ∈ θ := by
      rcases mem_succ_iff.mp hj with rfl | hj
      · exact (mem_irrefl k (hjk k hk)).elim
      · exact hj
    simp only [forcingFamilyNext_old hi, forcingFamilyNext_old hk, forcingFamilyNext_old hjold,
      forcingMatrixNext_old hi' hjold, forcingMatrixNext_old hj hk] at hf hp hb ⊢
    exact h.compatible j hjold k hk hij hjk f hf p hp hb

theorem forcingInitialBound_sectionCompatible {i P R π E I : V}
    (h : IsSplitForcingSystem (succ i) P π E)
    (m : IsFunctionalSplitForcingSystem (succ i) P π E) :
    IsSectionCompatibleForcingBound (succ i) P R π E (forcingInitialBound i P I) i I := by
  have hi : i ∈ succ i := mem_succ_self i
  constructor
  intro j hj k hk hij hjk f hf p hp _
  have hej : j = i := by
    rcases mem_succ_iff.mp hj with he | hji
    · exact he
    · exact (mem_irrefl j (hij j hji)).elim
  have hek : k = i := by
    rcases mem_succ_iff.mp hk with he | hki
    · exact he
    · exact (mem_irrefl k ((subset_trans hij hjk) k hki)).elim
  subst j k
  rw [forcingInitialBound, forcingFamilyNext_new,
    forcingIdentityBound_value (compose_function hf.1 (m.sectionMap i hi i hi (subset_refl _))) hp,
    forcingIdentityBound_value hf.1 hp, h.secId i hi p hp]

end ZFVP
