import ZFVP.ModelTheory.ForcingFiniteFunctions
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingModelSequences
import ZFVP.SetTheory.FiniteFunctionLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem finite_sequenceValue_surjective (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) {n : V} (hn : n ∈ (ω : V))
    {b : S.Model} (hb : b ∈ range (S.evaluationGraph C hC) ^ S.check n) :
    ∃ s : V, ∃ hsN : IsNameSequence S.P s, s ∈ C ^ n ∧ S.sequenceValue s hsN = b := by
  have hn' : S.check n ∈ (ω : S.Model) := by
    rw [← S.checkEmbedding.map_omega]
    exact (S.check_mem_iff n ω).mpr hn
  obtain ⟨c, hc, hvalues⟩ := finite_function_lift (S.evaluationGraph_mem_function C hC) hn' hb
  obtain ⟨s, hs, hsc⟩ := S.function_eq_check_of_finite hn hc
  let := IsFunction.of_mem hs
  have hd : domain s = n := domain_eq_of_mem_function hs
  have hsN : IsNameSequence S.P s := fun i hi ↦ hC _ (function_value_mem hs (hd ▸ hi))
  have hseq : S.sequenceValue s hsN ∈ range (S.evaluationGraph C hC) ^ S.check n := by
    rw [← hd]
    apply S.sequenceValue_mem_function
    intro i hi
    exact mem_range_of_kpair_mem ((S.pair_mem_evaluationGraph_iff C hC _ _).mpr
      ⟨s ‘ i, function_value_mem hs (hd ▸ hi), rfl, rfl⟩)
  let := IsFunction.of_mem hseq
  let := IsFunction.of_mem hb
  refine ⟨s, hsN, hs, functions_eq_of_domain_values ?_ ?_⟩
  · rw [domain_eq_of_mem_function hseq, domain_eq_of_mem_function hb]
  · intro x hx
    rw [domain_eq_of_mem_function hseq] at hx
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff n x).mp hx
    rw [S.sequenceValue_value s hsN (hd.symm ▸ hi)]
    have hv := hvalues (S.check i) ((S.check_mem_iff i n).mpr hi)
    rw [← hsc, S.check_value (hd.symm ▸ hi), S.evaluationGraph_value C hC _ (function_value_mem hs hi)] at hv
    exact hv

end ForcingContext
end ZFVP
