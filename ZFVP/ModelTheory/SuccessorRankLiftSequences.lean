import ZFVP.ModelTheory.SuccessorRankLiftChecks
import ZFVP.ModelTheory.ForcingRetractionSequences
import ZFVP.SetTheory.CnSequenceNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData

variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (hone : A.one = B.one)

include hG hone

set_option maxHeartbeats 800000 in
theorem function_mem_graph_domain_of_closed {γ : V} [IsOrdinal γ]
    (hγ : γ ∈ hierarchy δ) (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt B.P B.R α)
    {X f : B.Model} (hX : X ∈ domain (L.graph hπ)) (hf : f ∈ X ^ B.check γ) :
    f ∈ domain (L.graph hπ) := by
  let := L.source_correct.ordinal
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain hπ X).mp hX
  have hft : f ∈ ForcingContext.retractionInclusion A B hπ hG (A.ofName τ) ^ B.check γ := hf
  obtain ⟨s, hsN, hs, heq⟩ := ForcingContext.retractionInclusion_function_sequence_of_closed
    A B hπ hG hDC hclosed hft
  let := IsFunction.of_mem hs
  have hsV := (hierarchy_transitive δ).mem_trans hs
    (function_mem_hierarchy_limit L.source_correct.successor_closed hγ (L.source_correct.domain_closed hτ))
  have hseq := L.source_correct.sequenceName_closed L.one_mem_source hsV
  apply (L.graph_domain hπ f).mpr
  refine ⟨⟨sequenceName A.one s, sequenceName_isName A.top.1 hsN⟩, hseq, ?_⟩
  have he : B.ofName ⟨sequenceName A.one s, (sequenceName_isName A.top.1 hsN).mono hπ.inclusion⟩ =
      B.sequenceValue s (fun i hi ↦ (hsN i hi).mono hπ.inclusion) := by
    apply congrArg B.ofName
    apply Subtype.ext
    exact congrArg (fun one ↦ sequenceName one s) hone
  exact heq.symm.trans he.symm

end SuccessorRankLiftData
end ZFVP
