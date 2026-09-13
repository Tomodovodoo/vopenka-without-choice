import ZFVP.SetTheory.ForcingIterationDefinability
import ZFVP.SetTheory.UniformRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A definable stage rule preserving the coded invariant produces an internal history. -/
theorem forcingIteration_recursion_invariant (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hstep : ∀ θ : V, IsOrdinal θ → ∀ H, IsForcingIterationHistory θ H →
      IsForcingIterationCode (succ θ) (F H) ∧
      ForcingCodeExtends (forcingIterationCodeUnion θ H) (F H))
    (α : V) [IsOrdinal α] :
    IsForcingIterationCode (succ α) (Replacement.transfiniteRec F hF α) ∧
      ∀ i ∈ α, ForcingCodeExtends (Replacement.transfiniteRec F hF i)
        (Replacement.transfiniteRec F hF α) := by
  let r := Replacement.transfiniteRec F hF
  have dr : ℒₛₑₜ-function₁ r := Replacement.transfiniteRec_definable hF
  have hall := transfinite_induction
    (fun θ ↦ IsForcingIterationCode (succ θ) (r θ) ∧
      ∀ i ∈ θ, ForcingCodeExtends (r i) (r θ)) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal α)
  intro θ ih
  let H := definableGraph (θ : V) r dr
  have hv {i : V} (hi : i ∈ (θ : V)) : H ‘ i = r i := value_definableGraph _ _ _ hi
  have hh : IsForcingIterationHistory (θ : V) H := by
    refine ⟨⟨inferInstance, domain_definableGraph _ _ _⟩, ?_, ?_⟩
    · intro i hi
      have : IsOrdinal i := IsOrdinal.of_mem hi
      rw [hv hi]
      exact (ih (IsOrdinal.toOrdinal i) hi).1
    · intro i hi j hj hij
      have : IsOrdinal i := IsOrdinal.of_mem hi
      have : IsOrdinal j := IsOrdinal.of_mem hj
      rw [hv hi, hv hj]
      rcases IsOrdinal.subset_iff.mp hij with rfl | hij
      · exact ForcingCodeExtends.refl _
      · exact (ih (IsOrdinal.toOrdinal j) hj).2 i hij
  have hs := hstep θ inferInstance H hh
  have he : r θ = F H := Replacement.transfiniteRec_spec F hF θ
  rw [he]
  refine ⟨hs.1, ?_⟩
  intro i hi
  have hx := forcingIterationCodeUnion_extends (H := H) hi
  rw [hv hi] at hx
  exact hx.trans hs.2

theorem forcingIteration_recursion_history (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hstep : ∀ θ : V, IsOrdinal θ → ∀ H, IsForcingIterationHistory θ H →
      IsForcingIterationCode (succ θ) (F H) ∧
      ForcingCodeExtends (forcingIterationCodeUnion θ H) (F H))
    (α : V) [IsOrdinal α] :
    IsForcingIterationHistory α (definableGraph α (Replacement.transfiniteRec F hF)
      (Replacement.transfiniteRec_definable hF)) := by
  refine ⟨⟨inferInstance, domain_definableGraph _ _ _⟩, ?_, ?_⟩
  · intro i hi
    have : IsOrdinal i := IsOrdinal.of_mem hi
    rw [value_definableGraph _ _ _ hi]
    exact (forcingIteration_recursion_invariant F hF hstep i).1
  · intro i hi j hj hij
    have : IsOrdinal i := IsOrdinal.of_mem hi
    have : IsOrdinal j := IsOrdinal.of_mem hj
    rw [value_definableGraph _ _ _ hi, value_definableGraph _ _ _ hj]
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact ForcingCodeExtends.refl _
    · exact (forcingIteration_recursion_invariant F hF hstep j).2 i hij

end ZFVP
