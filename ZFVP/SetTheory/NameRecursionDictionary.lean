import ZFVP.SetTheory.ForcingDictionary
import ZFVP.SetTheory.NameActionClosure
import ZFVP.SetTheory.UniformLowTruth

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def checkNameStepFormula : SetTheorySemisentence 4 :=
  f“C o x g. ∀ z, z ∈ C ↔ ∃ y ∈ x, !kpair.dfn z (!value.dfn g y) o”

def checkNameTableFormula : SetTheorySemisentence 3 :=
  f“f o x. !IsFunction.dfn f ∧ !domain.dfn f = !transitiveClosureFormula (!singleton.dfn x) ∧
    ∀ t ∈ !transitiveClosureFormula (!singleton.dfn x),
      !value.dfn f t = !checkNameStepFormula o t (!restrict.dfn f t)”

def checkNameFormula : SetTheorySemisentence 3 :=
  f“y o x. ∃ f, !checkNameTableFormula f o x ∧ y = !value.dfn f x”

def nameActionStepFormula : SetTheorySemisentence 4 :=
  f“C p t g. ∀ z, z ∈ C ↔ ∃ w ∈ t,
    !kpair.dfn z (!value.dfn g (!kpair.π₁.dfn w)) (!value.dfn p (!kpair.π₂.dfn w))”

def nameActionTableFormula : SetTheorySemisentence 3 :=
  f“f p t. !IsFunction.dfn f ∧ !domain.dfn f = !nameClosureFormula t ∧
    ∀ s ∈ !nameClosureFormula t,
      !value.dfn f s = !nameActionStepFormula p s (!restrict.dfn f (!domain.dfn s))”

def nameActionFormula : SetTheorySemisentence 3 :=
  f“y p t. ∃ f, !nameActionTableFormula f p t ∧ y = !value.dfn f t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance checkNameStepFormula_defined : ℒₛₑₜ-function₃[V] checkNameStep via checkNameStepFormula :=
  ⟨fun v ↦ by
    change checkNameStepFormula.Evalb v ↔ v 0 = checkNameStep (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [checkNameStepFormula, checkNameStep, repl_spec]⟩

instance checkNameTableFormula_defined : ℒₛₑₜ-relation₃[V]
    (fun f o x ↦ IsMembershipRecursion (transitiveClosure ({x} : V)) (checkNameStep o) f)
    via checkNameTableFormula :=
  ⟨fun v ↦ by simp [checkNameTableFormula, IsMembershipRecursion]⟩

instance checkNameFormula_defined : ℒₛₑₜ-function₂[V] checkName via checkNameFormula :=
  ⟨fun v ↦ by
    change checkNameFormula.Evalb v ↔ v 0 = checkName (v 1) (v 2)
    rw [checkName_eq_iff]
    simp [checkNameFormula]⟩

instance nameActionStepFormula_defined : ℒₛₑₜ-function₃[V] nameActionStep via nameActionStepFormula :=
  ⟨fun v ↦ by
    change nameActionStepFormula.Evalb v ↔ v 0 = nameActionStep (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [nameActionStepFormula, nameActionStep, repl_spec]⟩

instance nameActionTableFormula_defined : ℒₛₑₜ-relation₃[V]
    (fun f p t ↦ IsSubnameRecursion (nameClosure t) (nameActionStep p) f) via nameActionTableFormula :=
  ⟨fun v ↦ by simp [nameActionTableFormula, IsSubnameRecursion]⟩

instance nameActionFormula_defined : ℒₛₑₜ-function₂[V] nameAction via nameActionFormula :=
  ⟨fun v ↦ by
    change nameActionFormula.Evalb v ↔ v 0 = nameAction (v 1) (v 2)
    rw [nameAction_eq_iff]
    simp [nameActionFormula]⟩

end ZFVP
