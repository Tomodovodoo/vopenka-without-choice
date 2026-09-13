import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingPreorderFormula : SetTheorySemisentence 2 :=
  f“P R. R ⊆ !prod.dfn P P ∧ (∀ p ∈ P, !kpair.dfn p p ∈ R) ∧
    ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
      !kpair.dfn p q ∈ R → !kpair.dfn q r ∈ R → !kpair.dfn p r ∈ R”

def forcingPosetFormula : SetTheorySemisentence 2 :=
  f“P R. !forcingPreorderFormula P R ∧ ∀ p ∈ P, ∀ q ∈ P,
    !kpair.dfn p q ∈ R → !kpair.dfn q p ∈ R → p = q”

def forcingTopFormula : SetTheorySemisentence 3 :=
  f“P R o. o ∈ P ∧ ∀ p ∈ P, !kpair.dfn p o ∈ R”

def forcingCompatibleFormula : SetTheorySemisentence 4 :=
  f“P R p q. ∃ r ∈ P, !kpair.dfn r p ∈ R ∧ !kpair.dfn r q ∈ R”

def forcingDenseBelowFormula : SetTheorySemisentence 4 :=
  f“P R D p. D ⊆ P ∧ ∀ q ∈ P, !kpair.dfn q p ∈ R → ∃ r ∈ D, !kpair.dfn r q ∈ R”

def forcingDenseFormula : SetTheorySemisentence 3 :=
  f“P R D. D ⊆ P ∧ ∀ p ∈ P, ∃ q ∈ D, !kpair.dfn q p ∈ R”

def subnameClosedFormula : SetTheorySemisentence 1 :=
  f“X. ∀ t ∈ X, !domain.dfn t ⊆ X”

def nameClosureFormula : SetTheorySemisentence 2 :=
  f“C t. t ∈ C ∧ !subnameClosedFormula C ∧
    ∀ X, !subnameClosedFormula X → t ∈ X → C ⊆ X”

def forcingNameFormula : SetTheorySemisentence 2 :=
  f“P t. ∀ s ∈ !nameClosureFormula t, ∀ z ∈ s, ∃ u, ∃ p ∈ P, !kpair.dfn z u p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingPreorderFormula_defined : ℒₛₑₜ-relation[V] IsForcingPreorder via forcingPreorderFormula :=
  ⟨fun v ↦ by simp [forcingPreorderFormula, IsForcingPreorder]⟩

instance forcingPosetFormula_defined : ℒₛₑₜ-relation[V] IsForcingPoset via forcingPosetFormula :=
  ⟨fun v ↦ by simp [forcingPosetFormula, IsForcingPoset]⟩

instance forcingTopFormula_defined : ℒₛₑₜ-relation₃[V] IsForcingTop via forcingTopFormula :=
  ⟨fun v ↦ by simp [forcingTopFormula, IsForcingTop]⟩

instance forcingCompatibleFormula_defined : ℒₛₑₜ-relation₄[V] ForcingCompatible via forcingCompatibleFormula :=
  ⟨fun v ↦ by simp [forcingCompatibleFormula, ForcingCompatible]⟩

instance forcingDenseBelowFormula_defined : ℒₛₑₜ-relation₄[V] ForcingDenseBelow via forcingDenseBelowFormula :=
  ⟨fun v ↦ by simp [forcingDenseBelowFormula, ForcingDenseBelow]⟩

instance forcingDenseFormula_defined : ℒₛₑₜ-relation₃[V] ForcingDense via forcingDenseFormula :=
  ⟨fun v ↦ by simp [forcingDenseFormula, ForcingDense]⟩

instance subnameClosedFormula_defined : ℒₛₑₜ-predicate[V] IsSubnameClosed via subnameClosedFormula :=
  ⟨fun v ↦ by simp [subnameClosedFormula, IsSubnameClosed]⟩

instance nameClosureFormula_defined : ℒₛₑₜ-function₁[V] nameClosure via nameClosureFormula :=
  ⟨fun v ↦ by
    change nameClosureFormula.Evalb v ↔ v 0 = nameClosure (v 1)
    rw [nameClosure_characterization]
    simp [nameClosureFormula]⟩

instance forcingNameFormula_defined : ℒₛₑₜ-relation[V] IsForcingName via forcingNameFormula :=
  ⟨fun v ↦ by simp [forcingNameFormula, IsForcingName]⟩

end ZFVP
