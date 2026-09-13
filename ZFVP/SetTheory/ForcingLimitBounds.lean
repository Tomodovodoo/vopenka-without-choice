import ZFVP.SetTheory.ForcingBoundThreads
import ZFVP.SetTheory.ForcingBoundExtension
import ZFVP.SetTheory.ForcingLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingBoundValue_family_definable (π B I i : V) :
    ℒₛₑₜ-function₃[V] (fun f p j ↦ forcingBoundValue π B I f i p j) := by
  classical
  have hh : ℒₛₑₜ-relation₄ (fun y f p j : V ↦
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
  apply Language.Definable.of_iff hh
  intro v
  change v 0 = forcingBoundValue π B I (v 1) i (v 2) (v 3) ↔ _
  by_cases he : v 3 ∈ i <;> simp [forcingBoundValue, he]

instance forcingBoundThread_family_definable (θ π B I i : V) :
    ℒₛₑₜ-function₂[V] (fun f p ↦ forcingBoundThread θ π B I f i p) := by
  have hh : ℒₛₑₜ-relation₃ (fun b f p : V ↦ ∀ z, z ∈ b ↔
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
          · apply Language.DefinableFunction₃.comp (F := fun f p j ↦ forcingBoundValue π B I f i p j) <;> definability
  apply Language.Definable.of_iff hh
  intro v
  change v 0 = forcingBoundThread θ π B I (v 1) i (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingBoundThread, mem_definableGraph_iff]

noncomputable def forcingLimitBound (θ P π B i I C : V) : V :=
  definableGraph ((C ^ I) ×ˢ (P ‘ i))
    (fun x ↦ forcingBoundThread θ π B I (kpair.π₁ x) i (kpair.π₂ x)) (by
      apply Language.DefinableFunction₂.comp (F := fun f p ↦ forcingBoundThread θ π B I f i p) <;> definability)

theorem forcingLimitBound_value {θ P π B i I C f p : V} (hf : f ∈ C ^ I) (hp : p ∈ P ‘ i) :
    (forcingLimitBound θ P π B i I C) ‘ ⟨f, p⟩ₖ = forcingBoundThread θ π B I f i p := by
  rw [forcingLimitBound, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hf, hp⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem forcingCoordinateFamily_compose {θ P π U I f j : V}
    (hf : f ∈ (forcingInverseLimit θ P π U) ^ I) (hj : j ∈ θ) :
    compose f (forcingThreadCoordinate (forcingInverseLimit θ P π U) j) = forcingCoordinateFamily I f j := by
  have hm := forcingThreadCoordinate_maps (P := P) (π := π) (U := U) hj
  have hc := compose_function hf hm
  have hjf := forcingCoordinateFamily_mem hf hj
  let := IsFunction.of_mem hc
  let := IsFunction.of_mem hjf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function hjf]
  · intro a ha
    rw [domain_eq_of_mem_function hc] at ha
    rw [value_compose_of_mem_function hf hm ha, forcingThreadCoordinate_value (function_value_mem hf ha),
      forcingCoordinateFamily_value ha]

end ZFVP
