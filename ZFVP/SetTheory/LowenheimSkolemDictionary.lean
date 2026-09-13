import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.ModelTheory.CodedEmbeddingTransport
import ZFVP.SetTheory.GroundUniquenessFormulas
import ZFVP.SetTheory.CofinalityDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lsMembershipRelationFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ z, z ∈ R ↔ z ∈ !prod.dfn D D ∧ !kpair.π₁.dfn z ∈ !kpair.π₂.dfn z”

def lsElementaryInclusionFormula : SetTheorySemisentence 2 :=
  f“A B. !codedMembershipEmbeddingFormula A B (!identity.dfn A)”

def smallTransitiveCollapseFormula : SetTheorySemisentence 2 :=
  f“κ X. ∃ C ∈ !hierarchyFormula κ, ∃ f,
    !isTransitiveCollapseFormula (!lsMembershipRelationFormula X) X C f”

def weaklyLSCardinalFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ !isω ∈ κ ∧
    ∀ γ ∈ κ, ∀ α, !IsOrdinal.dfn α → κ ⊆ α → ∀ x ∈ !hierarchyFormula α,
      ∃ X, !lsElementaryInclusionFormula X (!hierarchyFormula α) ∧
        !hierarchyFormula γ ⊆ X ∧ x ∈ X ∧ !smallTransitiveCollapseFormula κ X”

def lsCardinalFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ !isω ∈ κ ∧
    ∀ γ ∈ κ, ∀ α, !IsOrdinal.dfn α → κ ⊆ α → ∀ x ∈ !hierarchyFormula α,
      ∃ β X, !IsOrdinal.dfn β ∧ α ⊆ β ∧
        !lsElementaryInclusionFormula X (!hierarchyFormula β) ∧
        !hierarchyFormula γ ⊆ X ∧ x ∈ X ∧ !smallTransitiveCollapseFormula κ X ∧
        !function.dfn (!inter.dfn X (!hierarchyFormula α)) (!hierarchyFormula γ) ⊆ X”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance lsMembershipRelationFormula_defined :
    ℒₛₑₜ-function₁[V] membershipRelation via lsMembershipRelationFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [lsMembershipRelationFormula, membershipRelation]⟩

instance lsElementaryInclusionFormula_defined :
    ℒₛₑₜ-relation[V] IsElementaryInclusion via lsElementaryInclusionFormula :=
  ⟨fun v ↦ by simp [lsElementaryInclusionFormula, IsElementaryInclusion]⟩

instance smallTransitiveCollapseFormula_defined :
    ℒₛₑₜ-relation[V] HasSmallTransitiveCollapse via smallTransitiveCollapseFormula :=
  ⟨fun v ↦ by simp [smallTransitiveCollapseFormula, HasSmallTransitiveCollapse]⟩

instance weaklyLSCardinalFormula_defined :
    ℒₛₑₜ-predicate[V] IsWeaklyLSCardinal via weaklyLSCardinalFormula :=
  ⟨fun v ↦ by simp [weaklyLSCardinalFormula, IsWeaklyLSCardinal]⟩

instance lsCardinalFormula_defined : ℒₛₑₜ-predicate[V] IsLSCardinal via lsCardinalFormula :=
  ⟨fun v ↦ by simp [lsCardinalFormula, IsLSCardinal]⟩

end ZFVP
