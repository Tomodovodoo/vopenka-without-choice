import ZFVP.SetTheory.WoodinSeedInsertion
import ZFVP.SetTheory.BoundedSetUnionInter
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.LevyGraphAssembly

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinSourceIndexFormula : SetTheorySemisentence 2 := sigmaOneOrdinalLeftOneFormula

def piOneWoodinSourceIndexFormula : SetTheorySemisentence 2 :=
  “z θ. !IsOrdinal.dfn θ ∧ ∀ w, !sigmaOneWoodinSourceIndexFormula w θ → z = w”

def sigmaOneWoodinRecursiveIndexFormula : SetTheorySemisentence 2 :=
  “z β. ∃ w, !boundedOmegaFormula w ∧
    ((β ∈ w ∧ !boundedSUnionFormula z β) ∨ (β ∉ w ∧ z = β))”

def piOneWoodinRecursiveIndexFormula : SetTheorySemisentence 2 :=
  “z β. ∀ w, !sigmaOneWoodinRecursiveIndexFormula w β → z = w”

theorem sigmaOneWoodinSourceIndexFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSourceIndexFormula :=
  sigmaOneOrdinalLeftOneFormula_sigmaOne

theorem piOneWoodinSourceIndexFormula_piOne : IsPiFormula 1 piOneWoodinSourceIndexFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaOneWoodinSourceIndexFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

theorem sigmaOneWoodinRecursiveIndexFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinRecursiveIndexFormula :=
  .exs (.bounded (.and (boundedOmegaFormula_bounded.subst _)
    (.or (.and (.rel _ _) (boundedSUnionFormula_bounded.subst _)) (.and (.nrel _ _) (.rel _ _)))))

theorem piOneWoodinRecursiveIndexFormula_piOne : IsPiFormula 1 piOneWoodinRecursiveIndexFormula :=
  .all (.or (sigmaOneWoodinRecursiveIndexFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

def sigmaOneWoodinInsertSeedRow : SetTheorySemisentence 4 :=
  “z β f a. (!boundedEmptyFormula β ∧ z = a) ∨
    (¬!boundedEmptyFormula β ∧ ∃ i, !sigmaOneWoodinRecursiveIndexFormula i β ∧ !boundedValueFormula z f i)”

def sigmaOneWoodinInsertSeedFormula : SetTheorySemisentence 4 :=
  “G θ f a. ∃ D, !sigmaOneWoodinSourceIndexFormula D θ ∧
    !(graphAssemblyFormula sigmaOneWoodinInsertSeedRow) G D f a”

def piOneWoodinInsertSeedFormula : SetTheorySemisentence 4 :=
  “G θ f a. !IsOrdinal.dfn θ ∧ ∀ Q, !sigmaOneWoodinInsertSeedFormula Q θ f a → G = Q”

theorem sigmaOneWoodinInsertSeedRow_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinInsertSeedRow :=
  .or (.bounded (.and (boundedEmptyFormula_bounded.subst _) (.rel _ _)))
    (.and (.bounded (boundedEmptyFormula_bounded.subst _).neg)
      (.exs (.and (sigmaOneWoodinRecursiveIndexFormula_sigmaOne.subst _) (.bounded (boundedValueFormula_bounded.subst _)))))

theorem sigmaOneWoodinInsertSeedFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinInsertSeedFormula :=
  .exs (.and (sigmaOneWoodinSourceIndexFormula_sigmaOne.subst _)
    ((graphAssemblyFormula_levy sigmaOneWoodinInsertSeedRow_sigmaOne).subst _))

theorem piOneWoodinInsertSeedFormula_piOne : IsPiFormula 1 piOneWoodinInsertSeedFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneWoodinSourceIndexFormula_defined :
    ℒₛₑₜ-relation[V] (fun z θ ↦ IsOrdinal θ ∧ z = woodinSourceIndex θ) via sigmaOneWoodinSourceIndexFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    simpa only [sigmaOneWoodinSourceIndexFormula, woodinSourceIndex, hv] using
      eval_sigmaOneOrdinalLeftOneFormula (v 0) (v 1)⟩

instance piOneWoodinSourceIndexFormula_defined :
    ℒₛₑₜ-relation[V] (fun z θ ↦ IsOrdinal θ ∧ z = woodinSourceIndex θ) via piOneWoodinSourceIndexFormula :=
  ⟨fun v ↦ by simp [piOneWoodinSourceIndexFormula]; exact fun h ↦ Or.inl h⟩

instance sigmaOneWoodinRecursiveIndexFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecursiveIndex via sigmaOneWoodinRecursiveIndexFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ (ω : V) <;> simp [sigmaOneWoodinRecursiveIndexFormula, woodinRecursiveIndex, h]⟩

instance piOneWoodinRecursiveIndexFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecursiveIndex via piOneWoodinRecursiveIndexFormula :=
  ⟨fun v ↦ by simp [piOneWoodinRecursiveIndexFormula]⟩

instance sigmaOneWoodinInsertSeedRow_defined :
    ℒₛₑₜ-function₃[V] (fun β f a ↦ woodinInsertSeedValue f a β) via sigmaOneWoodinInsertSeedRow :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 = ∅ <;> simp [sigmaOneWoodinInsertSeedRow, woodinInsertSeedValue, h]⟩

theorem eval_woodinInsertSeedGraph (G D f a : V) :
    (graphAssemblyFormula sigmaOneWoodinInsertSeedRow).Evalb ![G, D, f, a] ↔
      G = definableGraph D (woodinInsertSeedValue f a) (by definability) :=
  eval_graphAssemblyFormula sigmaOneWoodinInsertSeedRow G D ![f, a] (woodinInsertSeedValue f a) _
    (fun x _ y ↦ by simp)

instance sigmaOneWoodinInsertSeedFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ f a ↦ IsOrdinal θ ∧ G = woodinInsertSeed θ f a)
      via sigmaOneWoodinInsertSeedFormula :=
  ⟨fun v ↦ by
    have he := fun D ↦ eval_woodinInsertSeedGraph (v 0) D (v 2) (v 3)
    simp only [Semiformula.Evalb] at he
    simp [sigmaOneWoodinInsertSeedFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he, woodinInsertSeed]⟩

instance piOneWoodinInsertSeedFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ f a ↦ IsOrdinal θ ∧ G = woodinInsertSeed θ f a)
      via piOneWoodinInsertSeedFormula :=
  ⟨fun v ↦ by simp [piOneWoodinInsertSeedFormula]; exact fun h ↦ Or.inl h⟩

end ZFVP
