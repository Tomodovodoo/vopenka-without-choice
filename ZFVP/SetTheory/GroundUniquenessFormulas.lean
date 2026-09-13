import ZFVP.SetTheory.GroundUniqueness
import ZFVP.SetTheory.MostowskiCollapse

/-! Parameter-free defining formulas for the cover and approximation predicates of
`ZFVP.SetTheory.GroundUniqueness` and for the two collapse side conditions of
`ZFVP.SetTheory.MostowskiCollapse`. Each formula is a literal transcription of the Lean
definition, so the `Defined` instances give the predicates as semisentences with no parameters
from the model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `A` has size below `d`. -/
def uSmallFormula : SetTheorySemisentence 2 :=
  f“d A. ∃ m ∈ d, !CardLE.dfn A m”

/-- `B` is covered by a member of `M` that `M` injects into an ordinal below `d`. -/
def mSmallFormula : SetTheorySemisentence 3 :=
  f“M d B. ∃ m ∈ d, ∃ C ∈ M, B ⊆ C ∧ ∃ g ∈ M, g ∈ !function.dfn m C ∧ !Injective.dfn g”

/-- `B` is covered by a member of `M` that `M` injects into `d`. -/
def mBoundedFormula : SetTheorySemisentence 3 :=
  f“M d B. ∃ C ∈ M, B ⊆ C ∧ ∃ g ∈ M, g ∈ !function.dfn d C ∧ !Injective.dfn g”

/-- `M` is closed under binary intersections. -/
def interClosedFormula : SetTheorySemisentence 1 :=
  f“M. ∀ x ∈ M, ∀ y ∈ M, !inter.dfn x y ∈ M”

/-- The `d`-cover property of `M` for subsets of `t`. -/
def hasSmallCoverFormula : SetTheorySemisentence 3 :=
  f“M d t. ∀ A, A ⊆ t → !uSmallFormula d A →
    ∃ B ∈ M, A ⊆ B ∧ B ⊆ t ∧ !mSmallFormula M d B”

/-- The `d`-approximation property of `M` for subsets of `t`. -/
def hasApproximationFormula : SetTheorySemisentence 3 :=
  f“M d t. ∀ A, A ⊆ t →
    (∀ B ∈ M, B ⊆ t → !mSmallFormula M d B → !inter.dfn A B ∈ M) → A ∈ M”

/-- `g` collapses the relation `R` on `D` onto the transitive set `C`. -/
def isTransitiveCollapseFormula : SetTheorySemisentence 4 :=
  f“R D C g. !IsTransitive.dfn C ∧ g ∈ !function.dfn C D ∧ !range.dfn g = C ∧
    (∀ x ∈ D, ∀ y ∈ D, !value.dfn g x = !value.dfn g y → x = y) ∧
    ∀ x ∈ D, ∀ y ∈ D, (!value.dfn g x ∈ !value.dfn g y ↔ !kpair.dfn x y ∈ R)”

/-- `R` separates the members of `D` by their `R`-predecessors in `D`. -/
def isExtensionalOnFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ x ∈ D, ∀ y ∈ D,
    (∀ z ∈ D, (!kpair.dfn z x ∈ R ↔ !kpair.dfn z y ∈ R)) → x = y”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance uSmallFormula_defined : ℒₛₑₜ-relation[V] USmall via uSmallFormula :=
  ⟨fun v ↦ by simp [uSmallFormula, USmall]⟩

instance mSmallFormula_defined : ℒₛₑₜ-relation₃[V] MSmall via mSmallFormula :=
  ⟨fun v ↦ by simp [mSmallFormula, MSmall]⟩

instance mBoundedFormula_defined : ℒₛₑₜ-relation₃[V] MBounded via mBoundedFormula :=
  ⟨fun v ↦ by simp [mBoundedFormula, MBounded]⟩

instance interClosedFormula_defined : ℒₛₑₜ-predicate[V] InterClosed via interClosedFormula :=
  ⟨fun v ↦ by simp [interClosedFormula, InterClosed]⟩

instance hasSmallCoverFormula_defined :
    ℒₛₑₜ-relation₃[V] HasSmallCover via hasSmallCoverFormula :=
  ⟨fun v ↦ by simp [hasSmallCoverFormula, HasSmallCover]⟩

instance hasApproximationFormula_defined :
    ℒₛₑₜ-relation₃[V] HasApproximation via hasApproximationFormula :=
  ⟨fun v ↦ by simp [hasApproximationFormula, HasApproximation]⟩

instance isTransitiveCollapseFormula_defined :
    ℒₛₑₜ-relation₄[V] IsTransitiveCollapse via isTransitiveCollapseFormula :=
  ⟨fun v ↦ by simp [isTransitiveCollapseFormula, IsTransitiveCollapse]⟩

instance isExtensionalOnFormula_defined :
    ℒₛₑₜ-relation[V] IsExtensionalOn via isExtensionalOnFormula :=
  ⟨fun v ↦ by simp [isExtensionalOnFormula, IsExtensionalOn]⟩

end ZFVP
