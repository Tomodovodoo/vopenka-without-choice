import PalomarBridge.Vocabulary

namespace PalomarDCBridge
open PalomarBridge

/-- Every nonempty internal set with a serial relation has an internal omega sequence
following that relation. Omega includes every natural number of the model. -/
def DependentChoice {M : Type u} (mem : M → M → Prop) [Nonempty M] : Prop :=
  ∀ A R, (∃ x, mem x A) →
    (∀ x, mem x A → ∃ y, mem y A ∧ mem (Coding.pair mem x y) R) →
    ∃ f, mem f (Coding.functions mem A (Coding.omega mem)) ∧
      ∀ n, mem n (Coding.omega mem) →
        mem (Coding.pair mem (Coding.value mem f n)
          (Coding.value mem f (Coding.succ mem n))) R

/-- Failure of the explicit disjoint-family transversal axiom in the shared vocabulary. -/
def FailureOfChoice {M : Type u} (mem : M → M → Prop) : Prop := ¬ HasChoice mem

/-- A set-sized model of ZF, the full parameterized VP scheme, DC, and failure of AC. -/
def HasZFVPDCNotChoiceModel : Prop :=
  ∃ (M : Type) (mem : M → M → Prop) (hne : Nonempty M),
    IsZF mem ∧ @Coding.Vopenka M mem hne ∧
      @DependentChoice M mem hne ∧ FailureOfChoice mem

end PalomarDCBridge
