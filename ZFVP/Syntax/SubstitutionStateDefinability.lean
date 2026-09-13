import ZFVP.Syntax.SubstitutionStates
import ZFVP.SetTheory.UniformRecursion

/-! Definability of the iteration with all carried parameters varying. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def packedSubstitutionStateStep (P g : V) : V :=
  naturalIterationStep (liftSubstitutionState (kpair.π₁ (kpair.π₁ P)) (kpair.π₂ (kpair.π₁ P)))
    (kpair.π₂ P) g

instance packedSubstitutionStateStep_definable : ℒₛₑₜ-function₂[V] packedSubstitutionStateStep := by
  have h : ℒₛₑₜ-relation₃ (fun z P g : V ↦
      (domain g = 0 ∧ z = kpair.π₂ P) ∨
      (domain g ≠ 0 ∧ z = liftSubstitutionState (kpair.π₁ (kpair.π₁ P))
        (kpair.π₂ (kpair.π₁ P)) (g ‘ (⋃ˢ domain g)))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = packedSubstitutionStateStep (v 1) (v 2) ↔ _
  unfold packedSubstitutionStateStep naturalIterationStep
  split <;> simp_all

noncomputable def packedSubstitutionStateAt (P k : V) : V :=
  Replacement.transfiniteRec (packedSubstitutionStateStep P) (by definability) k

instance packedSubstitutionStateAt_definable : ℒₛₑₜ-function₂[V] packedSubstitutionStateAt := by
  have h : ℒₛₑₜ-relation₃ (fun y P k : V ↦
      (∃ g, IsAttempt (packedSubstitutionStateStep P) k g ∧ y = packedSubstitutionStateStep P g) ∨
      (¬IsOrdinal k ∧ y = ∅)) := by
    unfold IsAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact transfiniteRec_eq_iff (packedSubstitutionStateStep (v 1)) (by definability) (v 2) (v 0)

noncomputable def substitutionStateAt (L Δ s k : V) : V :=
  packedSubstitutionStateAt ⟨⟨L, Δ⟩ₖ, s⟩ₖ k

instance substitutionStateAt_definable : ℒₛₑₜ-function₄[V] substitutionStateAt := by
  unfold substitutionStateAt
  definability

theorem substitutionStateAt_eq (L Δ s k : V) : substitutionStateAt L Δ s k =
    naturalIteration (liftSubstitutionState L Δ) (by definability) s k := by
  unfold substitutionStateAt packedSubstitutionStateAt naturalIteration
  congr 1
  funext g
  simp only [packedSubstitutionStateStep, kpair.π₁_kpair, kpair.π₂_kpair]

instance substitutionStates_definable : ℒₛₑₜ-function₃[V] substitutionStates := by
  have h : ℒₛₑₜ-relation₄ (fun G L Δ s : V ↦ ∀ p,
      p ∈ G ↔ ∃ k ∈ (ω : V), p = ⟨k, substitutionStateAt L Δ s k⟩ₖ) := by
    unfold substitutionStateAt
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = substitutionStates (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [substitutionStates, naturalIterationGraph, mem_definableGraph_iff, substitutionStateAt_eq]

end ZFVP
