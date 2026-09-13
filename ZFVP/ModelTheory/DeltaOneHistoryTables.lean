import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.BoundedRelationRange
import ZFVP.SetTheory.BoundedSetUnionInter
import ZFVP.SetTheory.ForcingIterationHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def historyTableValueRow (φ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  “y i H. ∃ s, !boundedValueFormula s H i ∧ !φ y s”

theorem historyTableValueRow_sigmaOne {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ) :
    IsSigmaFormula 1 (historyTableValueRow φ) :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (hφ.subst _))

def sigmaOneHistoryTableFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  “T θ H. ∃ G, !(graphAssemblyFormula (historyTableValueRow φ)) G θ H ∧
    ∃ R, !boundedRangeFormula R G ∧ !boundedSUnionFormula T R”

def piOneHistoryTableFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  “T θ H. ∀ G, !(graphAssemblyFormula (historyTableValueRow φ)) G θ H →
    ∀ R, !boundedRangeFormula R G → !boundedSUnionFormula T R”

theorem sigmaOneHistoryTableFormula_sigmaOne {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ) :
    IsSigmaFormula 1 (sigmaOneHistoryTableFormula φ) :=
  .exs (.and ((graphAssemblyFormula_levy (historyTableValueRow_sigmaOne hφ)).subst _)
    (.exs (.bounded (.and (boundedRangeFormula_bounded.subst _) (boundedSUnionFormula_bounded.subst _)))))

theorem piOneHistoryTableFormula_piOne {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ) :
    IsPiFormula 1 (piOneHistoryTableFormula φ) :=
  .all (.or ((graphAssemblyFormula_levy (historyTableValueRow_sigmaOne hφ)).subst _).neg
    (.all (.bounded (.or (boundedRangeFormula_bounded.subst _).neg (boundedSUnionFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_historyTableValueGraph (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] (G θ H : V) :
    (graphAssemblyFormula (historyTableValueRow φ)).Evalb ![G, θ, H] ↔
      G = definableGraph θ (fun i ↦ c (H ‘ i)) (by have := hc.to_definable; definability) := by
  exact eval_graphAssemblyFormula (historyTableValueRow φ) G θ ![H] (fun i ↦ c (H ‘ i)) _
    (fun i _ y ↦ by simp [historyTableValueRow])

instance sigmaOneHistoryTableFormula_defined (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] :
    ℒₛₑₜ-function₂ (fun θ H ↦ forcingHistoryTable θ H c hc.to_definable) via sigmaOneHistoryTableFormula φ :=
  ⟨fun v ↦ by
    have he := fun G : V ↦ eval_historyTableValueGraph c φ G (v 1) (v 2)
    simp only [Semiformula.Evalb] at he
    simp [sigmaOneHistoryTableFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he, range_definableGraph,
      forcingHistoryTable, iterationTableUnion]⟩

instance piOneHistoryTableFormula_defined (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] :
    ℒₛₑₜ-function₂ (fun θ H ↦ forcingHistoryTable θ H c hc.to_definable) via piOneHistoryTableFormula φ :=
  ⟨fun v ↦ by
    have he := fun G : V ↦ eval_historyTableValueGraph c φ G (v 1) (v 2)
    simp only [Semiformula.Evalb] at he
    simp [piOneHistoryTableFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he, range_definableGraph,
      forcingHistoryTable, iterationTableUnion]⟩

end ZFVP
