import ZFVP.ModelTheory.WoodinIterationInvariant
import ZFVP.ModelTheory.ForcingSuccessorDefinability
import ZFVP.SetTheory.ForcingIterationDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinIterationStage_definable : ℒₛₑₜ-function₃[V] woodinIterationStage := by
  unfold woodinIterationStage
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinIterationSuccessor_definable : ℒₛₑₜ-function₃[V] woodinIterationSuccessor := by
  unfold woodinIterationSuccessor
  dsimp only
  apply Language.DefinableFunction₅.comp
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₄.comp <;> definability
  · apply Language.DefinableFunction₅.comp
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₄.comp <;> definability
  · definability

instance woodinIterationCardinalNext_definable : ℒₛₑₜ-function₃[V] woodinIterationCardinalNext := by
  unfold woodinIterationCardinalNext
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₁.comp
    apply Language.DefinableFunction₁.comp
    apply Language.DefinableFunction₃.comp <;> definability

instance woodinIteration_definable : ℒₛₑₜ-relation₄[V] IsWoodinIteration := by
  have h : ℒₛₑₜ-relation₄ (fun δ θ s K : V ↦
      IsForcingIterationCode θ s ∧
      (IsFunction K ∧ domain K = θ) ∧
      (∀ i ∈ θ, IsWoodinStage (woodinIterationStage s K i)) ∧
      (∀ i ∈ θ, IsWoodinStageSmall (woodinIterationStage s K i)) ∧
      (∀ i ∈ θ, IsChoicelessInaccessible (K ‘ i)) ∧
      (∀ i ∈ θ, K ‘ i ∈ δ) ∧
      (∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → K ‘ i ∈ K ‘ j)) := by
    apply Language.Definable.and
    · definability
    · apply Language.Definable.and
      · definability
      · apply Language.Definable.and
        · apply Language.Definable.all
          apply Language.Definable.imp
          · definability
          · apply Language.DefinablePred.comp
            apply Language.DefinableFunction₃.comp <;> definability
        · apply Language.Definable.and
          · apply Language.Definable.all
            apply Language.Definable.imp
            · definability
            · apply Language.DefinablePred.comp
              apply Language.DefinableFunction₃.comp <;> definability
          · definability
  apply Language.Definable.of_iff h
  intro v
  exact ⟨fun h ↦ ⟨h.code, ⟨h.cardinals.function, h.cardinals.domain_eq⟩,
    h.stage, h.small, h.inaccessible, h.bounded, h.increasing⟩,
    fun h ↦ ⟨h.1, ⟨h.2.1.1, h.2.1.2⟩, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

end ZFVP
