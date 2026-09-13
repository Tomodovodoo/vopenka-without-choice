import ZFVP.SetTheory.ForcingLimitColumnDefinability
import ZFVP.ModelTheory.WoodinBoundDefinability
import ZFVP.ModelTheory.InverseTwoStepCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance forcingThreadCode_definable : ℒₛₑₜ-function₃[V] forcingThreadCode := by
  unfold forcingThreadCode
  apply forcingIterationCodeNext_comp <;> definability

instance forcingDirectCode_definable : ℒₛₑₜ-function₂[V] forcingDirectCode := by
  unfold forcingDirectCode
  apply Language.DefinableFunction₃.comp <;> definability

instance forcingInverseCode_definable : ℒₛₑₜ-function₂[V] forcingInverseCode := by
  unfold forcingInverseCode
  apply Language.DefinableFunction₃.comp <;> definability

instance forcingComposeProjectionColumn_definable :
    ℒₛₑₜ-function₃[V] forcingComposeProjectionColumn := by
  have h : ℒₛₑₜ-relation₄ (fun g θ ρ v : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, z = ⟨i, compose v (ρ ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingComposeProjectionColumn (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingComposeProjectionColumn, mem_definableGraph_iff]

instance forcingComposeSectionColumn_definable :
    ℒₛₑₜ-function₃[V] forcingComposeSectionColumn := by
  have h : ℒₛₑₜ-relation₄ (fun g θ F e : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, z = ⟨i, compose (F ‘ i) e⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingComposeSectionColumn (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingComposeSectionColumn, mem_definableGraph_iff]

instance forcingTwoStepLiftColumn_definable :
    ℒₛₑₜ-function₄[V] forcingTwoStepLiftColumn := by
  have h : ℒₛₑₜ-relation₅ (fun g θ D P M : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, z = ⟨i, successorForcingLift D (P ‘ i) (M ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingTwoStepLiftColumn (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingTwoStepLiftColumn, mem_definableGraph_iff]

instance twoStepSection_uniform_definable : ℒₛₑₜ-function₂[V] twoStepSection := by
  have h : ℒₛₑₜ-relation₃ (fun g P t : V ↦ ∀ z, z ∈ g ↔ ∃ p ∈ P, z = ⟨p, ⟨p, t⟩ₖ⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = twoStepSection (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [twoStepSection, mem_definableGraph_iff]

instance forcingInverseTwoStepCode_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingInverseTwoStepCode (V := V)) := by
  unfold forcingInverseTwoStepCode forcingTwoStepColumnCode
  dsimp only
  apply forcingIterationCodeNext_comp <;> definability

end ZFVP
