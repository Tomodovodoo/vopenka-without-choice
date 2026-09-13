import ZFVP.Syntax.PackedSatisfaction
import ZFVP.Syntax.UniformFormulas

/-! Shared parameter-free projections for the satisfaction parameter tuple. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def satisfactionParametersFormula : SetTheorySemisentence 5 :=
  f“P L Γ M e. P = !kpair.dfn (!kpair.dfn L Γ) (!kpair.dfn M e)”

def satLanguageFormula : SetTheorySemisentence 2 :=
  f“x P. x = !kpair.π₁.dfn (!kpair.π₁.dfn P)”

def satVariablesFormula : SetTheorySemisentence 2 :=
  f“x P. x = !kpair.π₂.dfn (!kpair.π₁.dfn P)”

def satStructureFormula : SetTheorySemisentence 2 :=
  f“x P. x = !kpair.π₁.dfn (!kpair.π₂.dfn P)”

def satFreeAssignmentFormula : SetTheorySemisentence 2 :=
  f“x P. x = !kpair.π₂.dfn (!kpair.π₂.dfn P)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance satisfactionParametersFormula_defined :
    ℒₛₑₜ-function₄[V] satisfactionParameters via satisfactionParametersFormula :=
  ⟨fun v ↦ by simp [satisfactionParametersFormula, satisfactionParameters]⟩

instance satLanguageFormula_defined : ℒₛₑₜ-function₁[V] satLanguage via satLanguageFormula :=
  ⟨fun v ↦ by simp [satLanguageFormula, satLanguage]⟩

instance satVariablesFormula_defined : ℒₛₑₜ-function₁[V] satVariables via satVariablesFormula :=
  ⟨fun v ↦ by simp [satVariablesFormula, satVariables]⟩

instance satStructureFormula_defined : ℒₛₑₜ-function₁[V] satStructure via satStructureFormula :=
  ⟨fun v ↦ by simp [satStructureFormula, satStructure]⟩

instance satFreeAssignmentFormula_defined : ℒₛₑₜ-function₁[V] satFreeAssignment via satFreeAssignmentFormula :=
  ⟨fun v ↦ by simp [satFreeAssignmentFormula, satFreeAssignment]⟩

end ZFVP

