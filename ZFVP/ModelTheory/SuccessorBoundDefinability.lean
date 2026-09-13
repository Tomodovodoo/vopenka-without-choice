import ZFVP.ModelTheory.WoodinSuccessorBoundTable
import ZFVP.ModelTheory.WoodinIterationDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance twoStepProjection_definable : ℒₛₑₜ-function₄[V] twoStepProjection := by
  have hd : ℒₛₑₜ-relation₅ (fun y P R Q t : V ↦ ∀ z, z ∈ y ↔
      ∃ x ∈ twoStepConditions P R Q t, z = ⟨x, kpair.π₁ x⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · apply Language.DefinableRel.comp (P := Membership.mem)
        · apply Language.DefinableFunction₄.comp (F := twoStepConditions) <;> definability
        · definability
      · definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = twoStepProjection (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [twoStepProjection, mem_definableGraph_iff]

instance forcingSuccessorBound_definable (I : V) :
    ℒₛₑₜ-function₄[V] (fun C A v b ↦ forcingSuccessorBound C A v b I) := by
  have hd : ℒₛₑₜ-relation₅ (fun y C A v b : V ↦ ∀ z, z ∈ y ↔
      ∃ x ∈ (C ^ I) ×ˢ A,
        z = ⟨x, twoStepUnionBound I (b ‘ ⟨compose (kpair.π₁ x) v, kpair.π₂ x⟩ₖ) (kpair.π₁ x)⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₃.comp (F := twoStepUnionBound) <;> definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = forcingSuccessorBound (v 1) (v 2) (v 3) (v 4) I ↔ _
  rw [mem_ext_iff]
  simp only [forcingSuccessorBound, mem_definableGraph_iff]

instance woodinSuccessorBoundTable_definable (s K i I : V) :
    ℒₛₑₜ-function₂[V] (fun k B ↦ woodinSuccessorBoundTable k s K B i I) := by
  unfold woodinSuccessorBoundTable
  dsimp only
  apply Language.DefinableFunction₃.comp (F := forcingFamilyNext)
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp (F := fun C A v b ↦ forcingSuccessorBound C A v b I)
    · apply Language.DefinableFunction₄.comp (F := twoStepConditions)
      · definability
      · definability
      · apply Language.DefinableFunction₅.comp (F := saturatedWoodinPrefixPosetName)
        · definability
        · definability
        · definability
        · definability
        · apply Language.DefinableFunction₄.comp (F := woodinPrefixCutoff) <;> definability
      · definability
    · definability
    · apply Language.DefinableFunction₄.comp (F := twoStepProjection)
      · definability
      · definability
      · apply Language.DefinableFunction₅.comp (F := saturatedWoodinPrefixPosetName)
        · definability
        · definability
        · definability
        · definability
        · apply Language.DefinableFunction₄.comp (F := woodinPrefixCutoff) <;> definability
      · definability
    · definability

end ZFVP
