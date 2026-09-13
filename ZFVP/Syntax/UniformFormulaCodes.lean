import ZFVP.Syntax.FormulaCodes
import ZFVP.Syntax.UniformTerms

/-! Shared first-order formulas for the eight constructors and valid atomic arguments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def relationTokenFormula : SetTheorySemisentence 2 :=
  f“t r. t = !kpair.dfn (!(numeralFormula 1)) r”

def truthCodeFormula : SetTheorySemisentence 1 :=
  f“t. t = !kpair.dfn (!(numeralFormula 0)) (!isEmpty)”

def falsityCodeFormula : SetTheorySemisentence 1 :=
  f“t. t = !kpair.dfn (!(numeralFormula 1)) (!isEmpty)”

def atomCodeFormula : SetTheorySemisentence 3 :=
  f“t x y. t = !kpair.dfn (!(numeralFormula 2)) (!kpair.dfn x y)”

def negAtomCodeFormula : SetTheorySemisentence 3 :=
  f“t x y. t = !kpair.dfn (!(numeralFormula 3)) (!kpair.dfn x y)”

def andCodeFormula : SetTheorySemisentence 3 :=
  f“t x y. t = !kpair.dfn (!(numeralFormula 4)) (!kpair.dfn x y)”

def orCodeFormula : SetTheorySemisentence 3 :=
  f“t x y. t = !kpair.dfn (!(numeralFormula 5)) (!kpair.dfn x y)”

def allCodeFormula : SetTheorySemisentence 2 :=
  f“t x. t = !kpair.dfn (!(numeralFormula 6)) x”

def existsCodeFormula : SetTheorySemisentence 2 :=
  f“t x. t = !kpair.dfn (!(numeralFormula 7)) x”

def isAtomicArgumentsFormula : SetTheorySemisentence 5 :=
  f“L Γ n r args. (r = !isEmpty ∧
    args ∈ !function.dfn (!termSetFormula L Γ n) (!(numeralFormula 2))) ∨
    ∃ s ∈ !relationSymbolsFormula L, r = !relationTokenFormula s ∧
      args ∈ !function.dfn (!termSetFormula L Γ n) (!value.dfn (!relationAritiesFormula L) s)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance relationTokenFormula_defined : ℒₛₑₜ-function₁[V] relationToken via relationTokenFormula :=
  ⟨fun v ↦ by simp [relationTokenFormula, relationToken]⟩

instance truthCodeFormula_defined : ℒₛₑₜ-function₀[V] (truthCode : V) via truthCodeFormula :=
  ⟨fun v ↦ by simp [truthCodeFormula, truthCode]⟩

instance falsityCodeFormula_defined : ℒₛₑₜ-function₀[V] (falsityCode : V) via falsityCodeFormula :=
  ⟨fun v ↦ by simp [falsityCodeFormula, falsityCode]⟩

instance atomCodeFormula_defined : ℒₛₑₜ-function₂[V] atomCode via atomCodeFormula :=
  ⟨fun v ↦ by simp [atomCodeFormula, atomCode]⟩

instance negAtomCodeFormula_defined : ℒₛₑₜ-function₂[V] negAtomCode via negAtomCodeFormula :=
  ⟨fun v ↦ by simp [negAtomCodeFormula, negAtomCode]⟩

instance andCodeFormula_defined : ℒₛₑₜ-function₂[V] andCode via andCodeFormula :=
  ⟨fun v ↦ by simp [andCodeFormula, andCode]⟩

instance orCodeFormula_defined : ℒₛₑₜ-function₂[V] orCode via orCodeFormula :=
  ⟨fun v ↦ by simp [orCodeFormula, orCode]⟩

instance allCodeFormula_defined : ℒₛₑₜ-function₁[V] allCode via allCodeFormula :=
  ⟨fun v ↦ by simp [allCodeFormula, allCode]⟩

instance existsCodeFormula_defined : ℒₛₑₜ-function₁[V] existsCode via existsCodeFormula :=
  ⟨fun v ↦ by simp [existsCodeFormula, existsCode]⟩

instance isAtomicArgumentsFormula_defined : Defined
    (fun v : Fin 5 → V ↦ IsAtomicArguments (v 0) (v 1) (v 2) (v 3) (v 4)) isAtomicArgumentsFormula :=
  ⟨fun v ↦ by simp [isAtomicArgumentsFormula, IsAtomicArguments, equalityToken]⟩

end ZFVP

