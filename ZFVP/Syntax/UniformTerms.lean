import ZFVP.Syntax.Terms
import ZFVP.ModelTheory.UniformCodes
import ZFVP.SetTheory.UniformNumerals

/-! Shared parameter-free definitions of internal term syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def syntaxUniverseFormula : SetTheorySemisentence 3 :=
  f“U L Γ. U = !codingUniverseFormula (!doubleton.dfn L Γ)”

def boundVarCodeFormula : SetTheorySemisentence 2 :=
  f“t i. t = !kpair.dfn (!(numeralFormula 0)) i”

def freeVarCodeFormula : SetTheorySemisentence 2 :=
  f“t x. t = !kpair.dfn (!(numeralFormula 1)) x”

def functionTermCodeFormula : SetTheorySemisentence 3 :=
  f“t f args. t = !kpair.dfn (!(numeralFormula 2)) (!kpair.dfn f args)”

def isTermClosedFormula : SetTheorySemisentence 4 :=
  f“L Γ n T. (∀ i ∈ n, !boundVarCodeFormula i ∈ T) ∧
    (∀ x ∈ Γ, !freeVarCodeFormula x ∈ T) ∧
    ∀ f ∈ !functionSymbolsFormula L,
      ∀ args ∈ !function.dfn T (!value.dfn (!functionAritiesFormula L) f),
        !functionTermCodeFormula f args ∈ T”

def termSetFormula : SetTheorySemisentence 4 :=
  f“X L Γ n. ∀ t, t ∈ X ↔ t ∈ !syntaxUniverseFormula L Γ ∧
    ∀ T, !isTermClosedFormula L Γ n T → t ∈ T”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance syntaxUniverseFormula_defined : ℒₛₑₜ-function₂[V] syntaxUniverse via syntaxUniverseFormula :=
  ⟨fun v ↦ by simp [syntaxUniverseFormula, syntaxUniverse, pair_eq_doubleton]⟩

instance boundVarCodeFormula_defined : ℒₛₑₜ-function₁[V] boundVarCode via boundVarCodeFormula :=
  ⟨fun v ↦ by simp [boundVarCodeFormula, boundVarCode]⟩

instance freeVarCodeFormula_defined : ℒₛₑₜ-function₁[V] freeVarCode via freeVarCodeFormula :=
  ⟨fun v ↦ by simp [freeVarCodeFormula, freeVarCode]⟩

instance functionTermCodeFormula_defined : ℒₛₑₜ-function₂[V] functionTermCode via functionTermCodeFormula :=
  ⟨fun v ↦ by simp [functionTermCodeFormula, functionTermCode]⟩

instance isTermClosedFormula_defined : ℒₛₑₜ-relation₄[V] IsTermClosed via isTermClosedFormula :=
  ⟨fun v ↦ by simp [isTermClosedFormula, IsTermClosed]⟩

instance termSetFormula_defined : ℒₛₑₜ-function₃[V] termSet via termSetFormula :=
  ⟨fun v ↦ by
    change termSetFormula.Evalb v ↔ v 0 = termSet (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [termSetFormula, mem_termSet_iff]⟩

end ZFVP
