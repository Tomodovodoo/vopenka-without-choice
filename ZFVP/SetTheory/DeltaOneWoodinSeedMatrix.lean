import ZFVP.SetTheory.DeltaOneWoodinSeedInsertion
import ZFVP.SetTheory.WoodinSeedMatrix
import ZFVP.SetTheory.DeltaOnePairProjections
import ZFVP.SetTheory.BoundedProduct

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinSeedMatrixRow : SetTheorySemisentence 4 :=
  “y z M C. ∃ i, !sigmaOnePairFirstFormula i z ∧ ∃ j, !sigmaOnePairSecondFormula j z ∧
    ((!boundedEmptyFormula i ∧ !boundedValueFormula y C j) ∨
      (¬!boundedEmptyFormula i ∧ ∃ a, !sigmaOneWoodinRecursiveIndexFormula a i ∧
        ∃ b, !sigmaOneWoodinRecursiveIndexFormula b j ∧ ∃ p, !boundedKpairFormula p a b ∧ !boundedValueFormula y M p))”

def sigmaOneWoodinSeedMatrixFormula : SetTheorySemisentence 4 :=
  “G θ M C. ∃ D, !sigmaOneWoodinSourceIndexFormula D θ ∧
    ∃ X, !boundedProductFormula X D D ∧ !(graphAssemblyFormula sigmaOneWoodinSeedMatrixRow) G X M C”

def piOneWoodinSeedMatrixFormula : SetTheorySemisentence 4 :=
  “G θ M C. !IsOrdinal.dfn θ ∧ ∀ Q, !sigmaOneWoodinSeedMatrixFormula Q θ M C → G = Q”

theorem sigmaOneWoodinSeedMatrixRow_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedMatrixRow :=
  .exs (.and (sigmaOnePairFirstFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOnePairSecondFormula_sigmaOne.subst _)
      (.or (.bounded (.and (boundedEmptyFormula_bounded.subst _) (boundedValueFormula_bounded.subst _)))
        (.and (.bounded (boundedEmptyFormula_bounded.subst _).neg)
          (.exs (.and (sigmaOneWoodinRecursiveIndexFormula_sigmaOne.subst _)
            (.exs (.and (sigmaOneWoodinRecursiveIndexFormula_sigmaOne.subst _)
              (.exs (.bounded (.and (boundedKpairFormula_bounded.subst _) (boundedValueFormula_bounded.subst _)))))))))))))

theorem sigmaOneWoodinSeedMatrixFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedMatrixFormula :=
  .exs (.and (sigmaOneWoodinSourceIndexFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedProductFormula_bounded.subst _))
      ((graphAssemblyFormula_levy sigmaOneWoodinSeedMatrixRow_sigmaOne).subst _))))

theorem piOneWoodinSeedMatrixFormula_piOne : IsPiFormula 1 piOneWoodinSeedMatrixFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaOneWoodinSeedMatrixFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneWoodinSeedMatrixRow_defined :
    ℒₛₑₜ-function₃[V] (fun z M C ↦ woodinSeedMatrixValue M C z) via sigmaOneWoodinSeedMatrixRow :=
  ⟨fun v ↦ by
    classical
    by_cases h : kpair.π₁ (v 1) = ∅
    · simp [sigmaOneWoodinSeedMatrixRow, woodinSeedMatrixValue, h]
    · have hn := ne_empty_iff_isNonempty.mp h
      simp [sigmaOneWoodinSeedMatrixRow, woodinSeedMatrixValue, h, hn]⟩

theorem eval_woodinSeedMatrixGraph (G X M C : V) :
    (graphAssemblyFormula sigmaOneWoodinSeedMatrixRow).Evalb ![G, X, M, C] ↔
      G = definableGraph X (woodinSeedMatrixValue M C) (by definability) :=
  eval_graphAssemblyFormula sigmaOneWoodinSeedMatrixRow G X ![M, C] (woodinSeedMatrixValue M C) _
    (fun x _ y ↦ by simp)

instance sigmaOneWoodinSeedMatrixFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ M C ↦ IsOrdinal θ ∧ G = woodinSeedMatrix θ M C)
      via sigmaOneWoodinSeedMatrixFormula :=
  ⟨fun v ↦ by
    have he := fun X ↦ eval_woodinSeedMatrixGraph (v 0) X (v 2) (v 3)
    simp only [Semiformula.Evalb] at he
    simp [sigmaOneWoodinSeedMatrixFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he, woodinSeedMatrix]⟩

instance piOneWoodinSeedMatrixFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ M C ↦ IsOrdinal θ ∧ G = woodinSeedMatrix θ M C)
      via piOneWoodinSeedMatrixFormula :=
  ⟨fun v ↦ by simp [piOneWoodinSeedMatrixFormula]; exact fun h ↦ Or.inl h⟩

end ZFVP
