import ZFVP.SetTheory.ForcingLimitBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingBoundValue_system_definable (i I : V) :
    Language.DefinableFunction₅ ℒₛₑₜ (fun π B f p j ↦ forcingBoundValue π B I f i p j) := by
  classical
  have hd : Language.DefinableRel₆ ℒₛₑₜ (fun y π B f p j : V ↦
      (j ∈ i ∧ y = (π ‘ ⟨j, i⟩ₖ) ‘ p) ∨
      (j ∉ i ∧ y = (B ‘ j) ‘ ⟨forcingCoordinateFamily I f j, p⟩ₖ)) := by
    apply Language.Definable.or
    · definability
    · apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := value)
          · definability
          · apply Language.DefinableFunction₂.comp (F := kpair)
            · apply Language.DefinableFunction₃.comp <;> definability
            · definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = forcingBoundValue (v 1) (v 2) I (v 3) i (v 4) (v 5) ↔ _
  by_cases he : v 5 ∈ i <;> simp [forcingBoundValue, he]

instance forcingBoundThread_system_definable (i I : V) :
    Language.DefinableFunction₅ ℒₛₑₜ (fun θ π B f p ↦ forcingBoundThread θ π B I f i p) := by
  have hd : Language.DefinableRel₆ ℒₛₑₜ (fun b θ π B f p : V ↦ ∀ z, z ∈ b ↔
      ∃ j ∈ θ, z = ⟨j, forcingBoundValue π B I f i p j⟩ₖ) := by
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
          · apply Language.DefinableFunction₅.comp (F := fun π B f p j ↦ forcingBoundValue π B I f i p j) <;> definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = forcingBoundThread (v 1) (v 2) (v 3) I (v 4) i (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [forcingBoundThread, mem_definableGraph_iff]

instance forcingLimitBound_system_definable (i I : V) :
    Language.DefinableFunction₅ ℒₛₑₜ (fun θ P π B C ↦ forcingLimitBound θ P π B i I C) := by
  have hd : Language.DefinableRel₆ ℒₛₑₜ (fun b θ P π B C : V ↦ ∀ z, z ∈ b ↔
      ∃ x ∈ (C ^ I) ×ˢ (P ‘ i),
        z = ⟨x, forcingBoundThread θ π B I (kpair.π₁ x) i (kpair.π₂ x)⟩ₖ) := by
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
          · apply Language.DefinableFunction₅.comp (F := fun θ π B f p ↦ forcingBoundThread θ π B I f i p) <;> definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = forcingLimitBound (v 1) (v 2) (v 3) (v 4) i I (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLimitBound, mem_definableGraph_iff]

end ZFVP


