import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSubsetProductFormula : SetTheorySemisentence 3 :=
  “ν X P. ∀ z ∈ ν, ∃ x ∈ X, ∃ p ∈ P, !boundedKpairFormula z x p”

theorem boundedSubsetProductFormula_bounded : IsBoundedSetFormula boundedSubsetProductFormula :=
  .all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 4)
    (boundedKpairFormula_bounded.subst _)))

def boundedNameHierarchyRowFormula : SetTheorySemisentence 5 :=
  “ν β f T P. ∃ γ ∈ β, ∃ Y ∈ T,
    !boundedPairMemberFormula f γ Y ∧ !boundedSubsetProductFormula ν Y P”

theorem boundedNameHierarchyRowFormula_bounded :
    IsBoundedSetFormula boundedNameHierarchyRowFormula :=
  .exs (.bvar 1) (.exs (.bvar 4) (.and
    (boundedPairMemberFormula_bounded.subst _)
    (boundedSubsetProductFormula_bounded.subst _)))

def piOneNameHierarchyTableFormula : SetTheorySemisentence 4 :=
  “f a T P. !boundedFunctionFormula f a T ∧
    ∀ β ∈ a, ∀ X ∈ T, !boundedPairMemberFormula f β X →
      ∀ ν, (ν ∈ X → !boundedNameHierarchyRowFormula ν β f T P) ∧
        (!boundedNameHierarchyRowFormula ν β f T P → ν ∈ X)”

theorem piOneNameHierarchyTableFormula_piOne :
    IsPiFormula 1 piOneNameHierarchyTableFormula :=
  .and (.bounded (boundedFunctionFormula_bounded.subst _))
    (.boundedAll (.bvar 1) (.boundedAll (.bvar 3) (.or
      (.bounded (boundedPairMemberFormula_bounded.subst _).neg)
      (.all (.and (.or (.bounded (.nrel _ _))
          (.bounded (boundedNameHierarchyRowFormula_bounded.subst _)))
        (.or (.bounded (boundedNameHierarchyRowFormula_bounded.subst _).neg)
          (.bounded (.rel _ _))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSubsetProductFormula (ν X P : V) :
    boundedSubsetProductFormula.Evalb ![ν, X, P] ↔ ν ⊆ X ×ˢ P := by
  simp [boundedSubsetProductFormula, subset_def, mem_prod_iff]

theorem eval_boundedNameHierarchyRowFormula (ν β f T P : V) :
    boundedNameHierarchyRowFormula.Evalb ![ν, β, f, T, P] ↔
      ∃ γ ∈ β, ∃ Y ∈ T, ⟨γ, Y⟩ₖ ∈ f ∧ ν ⊆ Y ×ˢ P := by
  simp [boundedNameHierarchyRowFormula, eval_boundedSubsetProductFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def]

theorem eval_piOneNameHierarchyTableFormula (f a T P : V) :
    piOneNameHierarchyTableFormula.Evalb ![f, a, T, P] ↔
      f ∈ T ^ a ∧ ∀ β ∈ a, ∀ X ∈ T, ⟨β, X⟩ₖ ∈ f →
        ∀ ν, ν ∈ X ↔ ∃ γ ∈ β, ∃ Y ∈ T, ⟨γ, Y⟩ₖ ∈ f ∧ ν ⊆ Y ×ˢ P := by
  simp [piOneNameHierarchyTableFormula, eval_boundedNameHierarchyRowFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, iff_iff_implies_and_implies]

end ZFVP
