import ZFVP.SetTheory.HartogsDictionary
import Foundation.FirstOrder.SetTheory.Function

/-! Nonprincipal internally complete ultrafilters on an ordinal, and the sentence
"omega_1 carries a nonprincipal omega_1-complete ultrafilter". -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isUltrafilterOnFormula : SetTheorySemisentence 2 :=
  f“U κ. U ⊆ !power.dfn κ ∧ κ ∈ U ∧ !isEmpty ∉ U ∧ (∀ A ∈ U, ∀ B ∈ U, !inter.dfn A B ∈ U) ∧
    (∀ A ∈ U, ∀ B, B ⊆ κ → A ⊆ B → B ∈ U) ∧ ∀ A, A ⊆ κ → A ∈ U ∨ !sdiff.dfn κ A ∈ U”

def isNonprincipalCompleteUltrafilterFormula : SetTheorySemisentence 2 :=
  f“U κ. !isUltrafilterOnFormula U κ ∧ (∀ α ∈ κ, !singleton.dfn α ∉ U) ∧
    ∀ δ ∈ κ, !isNonempty δ → ∀ f ∈ !function.dfn U δ, !sInter.dfn (!range.dfn f) ∈ U”

/-- `ω_1 = hartogsNumber ω` carries a nonprincipal internally `ω_1`-complete ultrafilter. -/
def omegaOneCompleteUltrafilterSInterSentence : SetTheorySentence :=
  f“∃ U, !isNonprincipalCompleteUltrafilterFormula U (!hartogsNumberFormula (!isω))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsUltrafilterOn (U κ : V) : Prop :=
  U ⊆ ℘ κ ∧ κ ∈ U ∧ (∅ : V) ∉ U ∧ (∀ A ∈ U, ∀ B ∈ U, A ∩ B ∈ U) ∧
    (∀ A ∈ U, ∀ B, B ⊆ κ → A ⊆ B → B ∈ U) ∧ ∀ A, A ⊆ κ → A ∈ U ∨ κ \ A ∈ U

instance isUltrafilterOnFormula_defined :
    ℒₛₑₜ-relation[V] IsUltrafilterOn via isUltrafilterOnFormula :=
  ⟨fun v ↦ by simp [isUltrafilterOnFormula, IsUltrafilterOn]⟩

instance isUltrafilterOn_definable : ℒₛₑₜ-relation[V] IsUltrafilterOn :=
  isUltrafilterOnFormula_defined.to_definable

/-- A nonprincipal ultrafilter closed under intersections of internal sequences of length
below `κ`. -/
def IsNonprincipalCompleteUltrafilter (U κ : V) : Prop :=
  IsUltrafilterOn U κ ∧ (∀ α ∈ κ, ({α} : V) ∉ U) ∧
    ∀ δ ∈ κ, IsNonempty δ → ∀ f ∈ U ^ δ, ⋂ˢ range f ∈ U

instance isNonprincipalCompleteUltrafilterFormula_defined :
    ℒₛₑₜ-relation[V] IsNonprincipalCompleteUltrafilter via isNonprincipalCompleteUltrafilterFormula :=
  ⟨fun v ↦ by simp [isNonprincipalCompleteUltrafilterFormula, IsNonprincipalCompleteUltrafilter]⟩

instance isNonprincipalCompleteUltrafilter_definable :
    ℒₛₑₜ-relation[V] IsNonprincipalCompleteUltrafilter :=
  isNonprincipalCompleteUltrafilterFormula_defined.to_definable

def OmegaOneCompleteUltrafilter (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∃ U : V, IsNonprincipalCompleteUltrafilter U (hartogsNumber (ω : V))

instance omegaOneCompleteUltrafilterSInterSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ OmegaOneCompleteUltrafilter V) omegaOneCompleteUltrafilterSInterSentence :=
  ⟨fun v ↦ by simp [omegaOneCompleteUltrafilterSInterSentence, OmegaOneCompleteUltrafilter]⟩

end ZFVP
