import ZFVP.SetTheory.ForcingCoordinateFamilies
import ZFVP.SetTheory.ForcingRelativeClosure
import ZFVP.SetTheory.ForcingMapExtension
import ZFVP.SetTheory.ForcingOrderExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A family of relative directed-bound operations at one fixed base and index set. -/
structure IsCoherentForcingBound (θ P R π B i I : V) : Prop where
  bound : (∀ j ∈ θ, i ⊆ j → ∀ f, IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f →
    ∀ p ∈ P ‘ i, (∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (B ‘ j) ‘ ⟨f, p⟩ₖ ∈ P ‘ j ∧
      (∀ a ∈ I, ⟨(B ‘ j) ‘ ⟨f, p⟩ₖ, f ‘ a⟩ₖ ∈ R ‘ j) ∧
      (π ‘ ⟨i, j⟩ₖ) ‘ ((B ‘ j) ‘ ⟨f, p⟩ₖ) = p)
  commute : (∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ f, IsForcingDirectedFamily (P ‘ k) (R ‘ k) I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (π ‘ ⟨i, k⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (π ‘ ⟨j, k⟩ₖ) ‘ ((B ‘ k) ‘ ⟨f, p⟩ₖ) =
        (B ‘ j) ‘ ⟨compose f (π ‘ ⟨j, k⟩ₖ), p⟩ₖ)

noncomputable def forcingBoundValue (π B I f i p j : V) : V := by
  classical
  exact if j ∈ i then (π ‘ ⟨j, i⟩ₖ) ‘ p else (B ‘ j) ‘ ⟨forcingCoordinateFamily I f j, p⟩ₖ

instance forcingBoundValue_index_definable (π B I f i p : V) :
    ℒₛₑₜ-function₁[V] (forcingBoundValue π B I f i p) := by
  classical
  have h : ℒₛₑₜ-relation (fun y j : V ↦
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
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingBoundValue π B I f i p (v 1) ↔ _
  by_cases he : v 1 ∈ i <;> simp [forcingBoundValue, he]

noncomputable def forcingBoundThread (θ π B I f i p : V) : V :=
  definableGraph θ (forcingBoundValue π B I f i p) (by infer_instance)

theorem forcingBoundThread_value {θ π B I f i p j : V} (hj : j ∈ θ) :
    (forcingBoundThread θ π B I f i p) ‘ j = forcingBoundValue π B I f i p j :=
  value_definableGraph _ _ _ hj

theorem forcingCoordinateFamily_below {θ P R π E U I f i j p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hf : f ∈ (forcingInverseLimit θ P π U) ^ I)
    (hb : ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i) :
    ∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ ((forcingCoordinateFamily I f j) ‘ a)⟩ₖ ∈ R ‘ i := by
  intro a ha
  rw [forcingCoordinateFamily_value ha,
    forcingInverseLimit_project_subset h (function_value_mem hf ha) hi hj hij]
  exact hb a ha

end ZFVP
