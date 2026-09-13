import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem nameSequence_of_mem_function (S : ForcingContext V) {C n s : V}
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) (hs : s ∈ C ^ n) : IsNameSequence S.P s := by
  intro i hi
  exact hC _ (function_value_mem hs (domain_eq_of_mem_function hs ▸ hi))

noncomputable def sequenceNameGraph (S : ForcingContext V) (C : V) : V :=
  definableGraph (finiteSequences C) (sequenceName S.one) (by definability)

theorem sequenceNameGraph_function (S : ForcingContext V) (C : V) :
    S.sequenceNameGraph C ∈ range (S.sequenceNameGraph C) ^ finiteSequences C := by
  unfold sequenceNameGraph
  rw [range_definableGraph]
  exact definableGraph_mem_function _ _ _

theorem sequenceNameGraph_names (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) : ∀ τ ∈ range (S.sequenceNameGraph C), IsForcingName S.P τ := by
  intro τ hτ
  obtain ⟨s, hsτ⟩ := mem_range_iff.mp hτ
  obtain ⟨hs, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ s τ).mp hsτ
  obtain ⟨n, _, hn⟩ := (mem_finiteSequences_iff C s).mp hs
  exact sequenceName_isName S.top.1 (S.nameSequence_of_mem_function hC hn)

noncomputable def sequenceEvaluationGraph (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) : S.Model :=
  compose (S.check (S.sequenceNameGraph C))
    (S.evaluationGraph (range (S.sequenceNameGraph C)) (S.sequenceNameGraph_names C hC))

theorem sequenceEvaluationGraph_function (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    S.sequenceEvaluationGraph C hC ∈
      range (S.evaluationGraph (range (S.sequenceNameGraph C)) (S.sequenceNameGraph_names C hC)) ^ S.check (finiteSequences C) :=
  compose_function ((S.check_function_iff _ _ _).mpr (S.sequenceNameGraph_function C))
    (S.evaluationGraph_mem_function _ _)

instance sequenceEvaluationGraph_isFunction (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) : IsFunction (S.sequenceEvaluationGraph C hC) :=
  IsFunction.of_mem (S.sequenceEvaluationGraph_function C hC)

theorem sequenceEvaluationGraph_value (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) {n s : V} (hn : n ∈ (ω : V)) (hs : s ∈ C ^ n) :
    (S.sequenceEvaluationGraph C hC) ‘ (S.check s) = S.sequenceValue s (S.nameSequence_of_mem_function hC hs) := by
  have hseq := (mem_finiteSequences_iff C s).mpr ⟨n, hn, hs⟩
  have hg := S.sequenceNameGraph_function C
  let := IsFunction.of_mem hg
  have hgval : (S.sequenceNameGraph C) ‘ s = sequenceName S.one s := value_definableGraph _ _ _ hseq
  have hname : sequenceName S.one s ∈ range (S.sequenceNameGraph C) := by
    rw [← hgval]
    exact function_value_mem hg hseq
  rw [sequenceEvaluationGraph, value_compose_of_mem_function ((S.check_function_iff _ _ _).mpr hg)
    (S.evaluationGraph_mem_function _ _) ((S.check_mem_iff _ _).mpr hseq)]
  rw [S.check_value (domain_eq_of_mem_function hg |>.symm ▸ hseq), hgval,
    S.evaluationGraph_value _ _ _ hname]
  rfl

end ForcingContext
end ZFVP
