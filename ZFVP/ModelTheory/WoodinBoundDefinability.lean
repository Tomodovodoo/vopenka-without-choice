import ZFVP.ModelTheory.SuccessorBoundDefinability
import ZFVP.ModelTheory.WoodinLimitBoundTable
import ZFVP.SetTheory.ForcingBoundSystemDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
instance woodinSuccessorBoundTable_uniform_definable (i I : V) :
    ℒₛₑₜ-function₄[V] (fun k s K B ↦ woodinSuccessorBoundTable k s K B i I) := by
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

instance forcingCodeUniverse_definable : ℒₛₑₜ-function₁[V] forcingCodeUniverse := by
  unfold forcingCodeUniverse
  definability

instance forcingInverseBoundTable_definable (i I : V) :
    ℒₛₑₜ-function₃[V] (fun θ s B ↦ forcingInverseBoundTable θ s B i I) := by
  unfold forcingInverseBoundTable
  apply Language.DefinableFunction₃.comp (F := forcingFamilyNext)
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp (F := fun θ P π B C ↦ forcingLimitBound θ P π B i I C)
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₄.comp (F := forcingInverseLimit) <;> definability

instance forcingDirectBoundTable_definable (i I : V) :
    ℒₛₑₜ-function₃[V] (fun θ s B ↦ forcingDirectBoundTable θ s B i I) := by
  unfold forcingDirectBoundTable
  apply Language.DefinableFunction₃.comp (F := forcingFamilyNext)
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp (F := fun θ P π B C ↦ forcingLimitBound θ P π B i I C)
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp (F := forcingDirectLimit) <;> definability

instance woodinLimitBaseBoundTable_definable (i I : V) :
    ℒₛₑₜ-function₄[V] (fun θ s K B ↦ woodinLimitBaseBoundTable θ s K B i I) := by
  classical
  have hd : ℒₛₑₜ-relation₅ (fun y θ s K B : V ↦
      (IsChoicelessInaccessible (woodinLimitCardinal K) ∧ y = forcingDirectBoundTable θ s B i I) ∨
      (¬IsChoicelessInaccessible (woodinLimitCardinal K) ∧ y = forcingInverseBoundTable θ s B i I)) := by
    apply Language.Definable.or
    · apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₃.comp (F := fun θ s B ↦ forcingDirectBoundTable θ s B i I) <;> definability
    · apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₃.comp (F := fun θ s B ↦ forcingInverseBoundTable θ s B i I) <;> definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinLimitBaseBoundTable (v 1) (v 2) (v 3) (v 4) i I ↔ _
  by_cases hh : IsChoicelessInaccessible (woodinLimitCardinal (v 3)) <;>
    simp [woodinLimitBaseBoundTable, hh]

end ZFVP


