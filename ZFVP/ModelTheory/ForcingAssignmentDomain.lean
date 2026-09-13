import ZFVP.ModelTheory.ForcingSequenceEvaluationGraph

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem sequenceValue_mem_evaluationRange (A : ForcingContext V) {D n b : V}
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hb : b ∈ D ^ n) :
    A.sequenceValue b (A.nameSequence_of_mem_function hD hb) ∈
      range (A.evaluationGraph D hD) ^ A.check n := by
  have hv := A.sequenceValue_mem_function b (A.nameSequence_of_mem_function hD hb)
    (A := range (A.evaluationGraph D hD)) (fun i hi ↦
      (A.mem_range_evaluationGraph_iff D hD _).mpr
        ⟨b ‘ i, function_value_mem hb (domain_eq_of_mem_function hb ▸ hi), rfl⟩)
  rwa [domain_eq_of_mem_function hb] at hv

end ForcingContext
end ZFVP
