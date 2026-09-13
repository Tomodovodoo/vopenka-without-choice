import ZFVP.SetTheory.WoodinCollapseDisplacement
import ZFVP.SetTheory.CollapseDictionary
import ZFVP.ModelTheory.UniformSparsePair
import ZFVP.ModelTheory.WoodinCollapseName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def collapseMembershipRelationFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ z, z ∈ R ↔ z ∈ !prod.dfn D D ∧ !kpair.π₁.dfn z ∈ !kpair.π₂.dfn z”

def freeCollapseRowFormula : SetTheorySemisentence 4 :=
  f“A κ p η. ∀ α, α ∈ A ↔ α ∈ κ ∧ !kpair.dfn α η ∉ !domain.dfn p”

def collapseRowMapFormula : SetTheorySemisentence 4 :=
  f“f κ p η. ∀ A, !freeCollapseRowFormula A κ p η →
    !mostowskiMapFormula f (!collapseMembershipRelationFormula A) A”

def collapseCoordinateValueFormula : SetTheorySemisentence 4 :=
  f“y κ p z. ∀ f, !collapseRowMapFormula f κ p (!kpair.π₂.dfn z) →
    y = !kpair.dfn (!value.dfn f (!kpair.π₁.dfn z)) (!kpair.π₂.dfn z)”

def collapseCoordinateMapFormula : SetTheorySemisentence 4 :=
  f“f κ δ p. ∀ z, z ∈ f ↔ ∃ x ∈ !prod.dfn κ δ,
    x ∉ !domain.dfn p ∧ z = !kpair.dfn x (!collapseCoordinateValueFormula κ p x)”

def collapseSupportMergeFormula : SetTheorySemisentence 5 :=
  f“r κ δ p q. ∀ z, z ∈ r ↔ z ∈ p ∨
    (z ∈ q ∧ ∃ x ∈ !prod.dfn κ δ, x ∉ !domain.dfn p ∧ ∃ y, z = !kpair.dfn x y)”

def collapseSupportInjectionFormula : SetTheorySemisentence 5 :=
  f“f κ δ p q. ∀ r C, !collapseSupportMergeFormula r κ δ p q →
    !collapseCoordinateMapFormula C κ δ r →
    ∀ z, z ∈ f ↔ ∃ x ∈ !domain.dfn p,
      z = !kpair.dfn x (!value.dfn (!sparseConverseGraphFormula C) x)”

def disjointSwapValueFormula : SetTheorySemisentence 4 :=
  f“y A f x. (x ∈ A ∧ y = !value.dfn f x) ∨
    (x ∉ A ∧ x ∈ !range.dfn f ∧ y = !value.dfn (!sparseConverseGraphFormula f) x) ∨
    (x ∉ A ∧ x ∉ !range.dfn f ∧ y = x)”

def disjointSwapFormula : SetTheorySemisentence 4 :=
  f“g I A f. ∀ z, z ∈ g ↔ ∃ x ∈ I, z = !kpair.dfn x (!disjointSwapValueFormula A f x)”

def woodinCollapseDisplacingCoordinatesFormula : SetTheorySemisentence 5 :=
  f“g κ δ p q. ∀ f, !collapseSupportInjectionFormula f κ δ p q →
    !disjointSwapFormula g (!prod.dfn κ δ) (!domain.dfn p) f”

def permutedCollapseGraphFormula : SetTheorySemisentence 3 :=
  f“q π p. ∀ z, z ∈ q ↔ ∃ u ∈ p,
    z = !kpair.dfn (!value.dfn π (!kpair.π₁.dfn u)) (!kpair.π₂.dfn u)”

def woodinCollapseDisplacementFormula : SetTheorySemisentence 5 :=
  f“f κ δ p q. ∀ π Q, !woodinCollapseDisplacingCoordinatesFormula π κ δ p q →
    !totalWoodinCollapseFormula Q κ δ →
    ∀ z, z ∈ f ↔ ∃ r ∈ Q, z = !kpair.dfn r (!permutedCollapseGraphFormula π r)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance collapseMembershipRelationFormula_defined :
    ℒₛₑₜ-function₁[V] membershipRelation via collapseMembershipRelationFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [collapseMembershipRelationFormula, membershipRelation]⟩

instance freeCollapseRowFormula_defined :
    ℒₛₑₜ-function₃[V] freeCollapseRow via freeCollapseRowFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [freeCollapseRowFormula, mem_freeCollapseRow]⟩

instance collapseRowMapFormula_defined :
    ℒₛₑₜ-function₃[V] collapseRowMap via collapseRowMapFormula :=
  ⟨fun v ↦ by simp [collapseRowMapFormula, collapseRowMap]⟩

instance collapseCoordinateValueFormula_defined :
    ℒₛₑₜ-function₃[V] collapseCoordinateValue via collapseCoordinateValueFormula :=
  ⟨fun v ↦ by simp [collapseCoordinateValueFormula, collapseCoordinateValue]⟩

instance collapseCoordinateMapFormula_defined :
    ℒₛₑₜ-function₃[V] collapseCoordinateMap via collapseCoordinateMapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [collapseCoordinateMapFormula, collapseCoordinateMap, mem_definableGraph_iff, freeCollapseCoordinates]
    simp only [and_assoc]⟩

instance collapseSupportMergeFormula_defined :
    ℒₛₑₜ-function₄[V] collapseSupportMerge via collapseSupportMergeFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [collapseSupportMergeFormula, collapseSupportMerge, mem_restrict_iff, and_assoc]⟩

instance collapseSupportInjectionFormula_defined :
    ℒₛₑₜ-function₄[V] collapseSupportInjection via collapseSupportInjectionFormula :=
  ⟨fun v ↦ by
    simp [collapseSupportInjectionFormula]
    rw [mem_ext_iff]
    simp [collapseSupportInjection, mem_definableGraph_iff]⟩

instance disjointSwapValueFormula_defined :
    ℒₛₑₜ-function₃[V] disjointSwapValue via disjointSwapValueFormula :=
  ⟨fun v ↦ by

    classical
    by_cases ha : v 3 ∈ v 1 <;> by_cases hf : v 3 ∈ range (v 2) <;>
      simp [disjointSwapValueFormula, disjointSwapValue, ha, hf]⟩

instance disjointSwapFormula_defined :
    ℒₛₑₜ-function₃[V] disjointSwap via disjointSwapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [disjointSwapFormula, disjointSwap, mem_definableGraph_iff]⟩

instance woodinCollapseDisplacingCoordinatesFormula_defined :
    ℒₛₑₜ-function₄[V] woodinCollapseDisplacingCoordinates via woodinCollapseDisplacingCoordinatesFormula :=
  ⟨fun v ↦ by simp [woodinCollapseDisplacingCoordinatesFormula, woodinCollapseDisplacingCoordinates]⟩

instance permutedCollapseGraphFormula_defined :
    ℒₛₑₜ-function₂[V] permutedGraph via permutedCollapseGraphFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [permutedCollapseGraphFormula, permutedGraph, permutedGraphEntry, repl_spec]⟩

noncomputable def totalWoodinCollapseDisplacement (κ δ p q : V) : V :=
  definableGraph (totalWoodinCollapse κ δ)
    (permutedGraph (woodinCollapseDisplacingCoordinates κ δ p q)) (by definability)

instance woodinCollapseDisplacementFormula_defined :
    ℒₛₑₜ-function₄[V] totalWoodinCollapseDisplacement via woodinCollapseDisplacementFormula :=
  ⟨fun v ↦ by
    simp [woodinCollapseDisplacementFormula]
    rw [mem_ext_iff]
    simp [totalWoodinCollapseDisplacement, mem_definableGraph_iff]⟩

theorem totalWoodinCollapseDisplacement_eq (κ δ p q : V) [IsOrdinal δ] :
    totalWoodinCollapseDisplacement κ δ p q = woodinCollapseDisplacement κ δ p q := by
  simp only [totalWoodinCollapseDisplacement, totalWoodinCollapse_eq,
    woodinCollapseDisplacement, woodinCollapsePermutation]
end ZFVP


