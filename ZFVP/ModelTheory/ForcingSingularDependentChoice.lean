import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.DependentChoiceCofinality
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_cofinalMap (A : ForcingContext V) {α β f : V} (hf : IsCofinalMap α β f) :
    IsCofinalMap (A.check α) (A.check β) (A.check f) := by
  let := IsFunction.of_mem hf.1
  refine ⟨(A.check_function_iff f β α).mpr hf.1, ?_⟩
  intro x hx
  obtain ⟨ξ, hξ, rfl⟩ := (A.mem_check_iff α x).mp hx
  obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ
  refine ⟨A.check i, (A.check_mem_iff _ _).mpr hi, ?_⟩
  rw [A.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hi)]
  exact (A.checkEmbedding.subset_iff _ _).mpr hξi

theorem check_cofinality_subset (A : ForcingContext V) (γ : V) [IsOrdinal γ] :
    internalCofinality (A.check γ) ⊆ A.check (internalCofinality γ) := by
  obtain ⟨f, hf⟩ := cofinalMap_exists γ
  exact internalCofinality_minimal (A.check_cofinalMap hf)

/-- At a ground singular limit, the shorter instances already supply DC at
the whole limit. A checked ground cofinal map still witnesses singularity. -/
theorem check_dependentChoiceAt_of_singular (A : ForcingContext V) {γ : V} [IsOrdinal γ]
    (h0 : ∅ ∈ γ) (hs : ∀ α ∈ γ, succ α ∈ γ)
    (hcf : internalCofinality γ ∈ γ)
    (hDC : ∀ α ∈ A.check γ, InternalDependentChoiceAt α) :
    InternalDependentChoiceAt (A.check γ) := by
  apply dependentChoiceAt_of_cofinality
  · simpa only [zero_def, A.check_empty] using (A.check_mem_iff ∅ γ).mpr h0
  · intro α hα
    obtain ⟨β, hβ, rfl⟩ := (A.mem_check_iff γ α).mp hα
    rw [← A.check_succ]
    exact (A.check_mem_iff _ _).mpr (hs β hβ)
  · exact hDC
  · exact hDC _ (ordinal_mem_of_subset_mem (A.check_cofinality_subset γ)
      ((A.check_mem_iff _ _).mpr hcf))

end ForcingContext
end ZFVP
