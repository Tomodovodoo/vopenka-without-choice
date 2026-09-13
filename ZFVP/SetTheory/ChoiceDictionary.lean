import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.UniformRank

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def choiceFunctionSentence : SetTheorySentence :=
  f“∀ A, (∀ X ∈ A, !isNonempty X) → ∃ f ∈ !function.dfn (!sUnion.dfn A) A,
    ∀ X ∈ A, !value.dfn f X ∈ X”

def dependentChoiceSentence : SetTheorySentence :=
  f“∀ A R, !isNonempty A → (∀ x ∈ A, ∃ y ∈ A, !kpair.dfn x y ∈ R) →
    ∃ f ∈ !function.dfn A (!isω), ∀ n ∈ !isω,
      !kpair.dfn (!value.dfn f n) (!value.dfn f (!succ.dfn n)) ∈ R”

def pointedDependentChoiceSentence : SetTheorySentence :=
  f“∀ A R a, a ∈ A → (∀ x ∈ A, ∃ y ∈ A, !kpair.dfn x y ∈ R) →
    ∃ f ∈ !function.dfn A (!isω), !value.dfn f (!isEmpty) = a ∧ ∀ n ∈ !isω,
      !kpair.dfn (!value.dfn f n) (!value.dfn f (!succ.dfn n)) ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance choiceFunctionSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ InternalChoice V) choiceFunctionSentence :=
  ⟨fun v ↦ by simp [choiceFunctionSentence, InternalChoice]⟩

instance dependentChoiceSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ InternalDependentChoice V) dependentChoiceSentence :=
  ⟨fun v ↦ by simp [dependentChoiceSentence, InternalDependentChoice]⟩

instance pointedDependentChoiceSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ InternalPointedDependentChoice V) pointedDependentChoiceSentence :=
  ⟨fun v ↦ by simp [pointedDependentChoiceSentence, InternalPointedDependentChoice, zero_def]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalChoice_iff (j : ElementaryMap V W) : InternalChoice V ↔ InternalChoice W :=
  j.map_defined choiceFunctionSentence (fun _ ↦ InternalChoice V) (fun _ ↦ InternalChoice W) ![]

theorem dependentChoice_iff (j : ElementaryMap V W) : InternalDependentChoice V ↔ InternalDependentChoice W :=
  j.map_defined dependentChoiceSentence (fun _ ↦ InternalDependentChoice V) (fun _ ↦ InternalDependentChoice W) ![]

theorem pointedDependentChoice_iff (j : ElementaryMap V W) :
    InternalPointedDependentChoice V ↔ InternalPointedDependentChoice W :=
  j.map_defined pointedDependentChoiceSentence (fun _ ↦ InternalPointedDependentChoice V)
    (fun _ ↦ InternalPointedDependentChoice W) ![]

end ElementaryMap
end ZFVP
