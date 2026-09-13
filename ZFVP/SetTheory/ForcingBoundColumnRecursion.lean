import ZFVP.SetTheory.ForcingBoundBaseSteps
import ZFVP.SetTheory.ForcingBoundRecursion
import ZFVP.ModelTheory.ForcingSuccessorDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingBoundColumnStep (P i I : V) (M : V → V → V) (θ B : V) : V := by
  classical
  exact forcingFamilyNext θ B (if θ ∈ i then ∅ else
    if θ = i then forcingIdentityBound (P ‘ i) I else M θ B)

theorem forcingBoundColumnStep_definable (P i I : V) (M : V → V → V)
    (hM : ℒₛₑₜ-function₂ M) : ℒₛₑₜ-function₂ (forcingBoundColumnStep P i I M) := by
  classical
  have hd : ℒₛₑₜ-relation₃ (fun y θ B : V ↦
      (θ ∈ i ∧ y = ∅) ∨
      (θ ∉ i ∧ θ = i ∧ y = forcingIdentityBound (P ‘ i) I) ∨
      (θ ∉ i ∧ θ ≠ i ∧ y = M θ B)) := by definability
  have hv : ℒₛₑₜ-function₂ (fun θ B : V ↦ if θ ∈ i then ∅ else
      if θ = i then forcingIdentityBound (P ‘ i) I else M θ B) := by
    apply Language.Definable.of_iff hd
    intro v
    change v 0 = (if v 1 ∈ i then ∅ else if v 1 = i then forcingIdentityBound (P ‘ i) I else M (v 1) (v 2)) ↔ _
    by_cases hh : v 1 ∈ i <;> by_cases he : v 1 = i <;> simp [hh, he]
  unfold forcingBoundColumnStep
  exact Language.DefinableFunction₃.comp (F := forcingFamilyNext)
    (by definability) (by definability) hv

theorem forcingBound_column_recursion {η P R π E i I : V} [IsOrdinal η] [IsOrdinal i]
    (M : V → V → V) (hM : ℒₛₑₜ-function₂ M) (ρ F : V → V)
    (hπ : ∀ θ ∈ succ η, π ‘ ⟨θ, θ⟩ₖ = identity (P ‘ θ))
    (hE : ∀ θ ∈ succ η, E ‘ ⟨θ, θ⟩ₖ = identity (P ‘ θ))
    (hρ : ∀ θ ∈ succ η, ∀ j ∈ θ, (ρ θ) ‘ j = π ‘ ⟨j, θ⟩ₖ)
    (hF : ∀ θ ∈ succ η, ∀ j ∈ θ, (F θ) ‘ j = E ‘ ⟨j, θ⟩ₖ)
    (hc : ∀ θ ∈ succ η, IsOrdinal θ → i ∈ θ → ∀ B,
      IsIterationTable θ B → IsCoherentForcingBound θ P R π B i I →
      IsSectionCompatibleForcingBound θ P R π E B i I →
      IsCoherentForcingBoundColumn θ P R B (P ‘ θ) (R ‘ θ) (ρ θ) (M θ B) i I ∧
      IsSectionCompatibleBoundColumn θ P R π B (F θ) (M θ B) i I) :
    let b := Replacement.transfiniteRec (forcingBoundRecursionStep (forcingBoundColumnStep P i I M))
      (forcingBoundRecursionStep_definable _ (forcingBoundColumnStep_definable P i I M hM)) η
    IsIterationTable (succ η) b ∧ IsCoherentForcingBound (succ η) P R π b i I ∧
      IsSectionCompatibleForcingBound (succ η) P R π E b i I := by
  classical
  apply forcingBound_recursion (forcingBoundColumnStep P i I M)
    (forcingBoundColumnStep_definable P i I M hM)
  intro θ hθη ho B ht hb hs
  let := ho
  rcases IsOrdinal.mem_trichotomy θ i with hθi | rfl | hiθ
  · have hsub : succ θ ⊆ i := by
      intro j hj
      rcases mem_succ_iff.mp hj with rfl | hj
      · exact hθi
      · exact IsOrdinal.toIsTransitive.mem_trans hj hθi
    simpa only [forcingBoundColumnStep, ite_eq_left hθi] using
      forcingBound_step_before_base (P := P) (R := R) (π := π) (E := E) (I := I) hsub ht
  · simpa only [forcingBoundColumnStep, mem_irrefl, ite_false, ite_true] using
      forcingBound_step_at_base (I := I) ht (hπ θ hθη) (hE θ hθη)
  · have hn : θ ∉ i := by
      intro hh
      exact mem_irrefl i (IsOrdinal.toIsTransitive.mem_trans hiθ hh)
    have he : θ ≠ i := (ne_of_mem hiθ).symm
    simp only [forcingBoundColumnStep, ite_eq_right hn, ite_eq_right he]
    obtain ⟨hcB, hsB⟩ := hc θ hθη ho hiθ B ht hb hs
    exact ⟨forcingFamilyNext_table _ _ _, hb.extend_fixed hcB hiθ (hρ θ hθη) (hπ θ hθη),
      hs.extend_fixed hcB hsB hiθ (hρ θ hθη i hiθ) (hF θ hθη) (hE θ hθη),
      forcingFamilyNext_extends ht _⟩

end ZFVP
