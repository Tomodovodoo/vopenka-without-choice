import ZFVP.ModelTheory.QuotientSplitProjection
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.ModelTheory.ForcingCompositionName
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V)

theorem projectionQuotient_sequence_eq {Q T π τ ρ : V} {f α : A.Model}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T) (hρ : ρ ∈ T ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (hf : f ∈ A.projectionQuotient Q π ^ α) :
    compose f (A.check ρ) = compose f (A.projectionQuotientMap Q π ρ) := by
  let := IsFunction.of_mem hρ
  have hfcheck := mem_function_of_mem_function_of_subset hf sep_subset
  have hc := (A.check_function_iff ρ Q T).mpr hρ
  have hm := A.projectionQuotientMap_maps hπ hτ hρ he
  have hl := compose_function hfcheck hc
  have hr := compose_function hf hm
  let := IsFunction.of_mem hl
  let := IsFunction.of_mem hr
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hl, domain_eq_of_mem_function hr]
  · intro i hi
    have hiα : i ∈ α := (domain_eq_of_mem_function hl) ▸ hi
    have hfi := function_value_mem hf hiα
    obtain ⟨q, hq, _, heq⟩ := (A.mem_projectionQuotient_iff hπ _).mp hfi
    rw [value_compose_of_mem_function hfcheck hc hiα,
      value_compose_of_mem_function hf hm hiα, heq]
    rw [A.projectionQuotientMap_value hρ hq (heq ▸ hfi)]
    exact A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hq)

theorem projectionQuotient_sequence_descending {Q S T U π τ ρ : V}
    {f α : A.Model} [IsOrdinal α]
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (hf : IsForcingDescending (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α f) :
    IsForcingDescending (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α
      (compose f (A.check ρ)) := by
  rw [A.projectionQuotient_sequence_eq hπ hτ hρ.maps he hf.1]
  have hp := A.projectionQuotient_projection hπ hτ hρ he
  refine ⟨compose_function hf.1 hp.maps, ?_⟩
  intro i hi j hj
  rw [value_compose_of_mem_function hf.1 hp.maps hi,
    value_compose_of_mem_function hf.1 hp.maps (IsOrdinal.toIsTransitive.mem_trans hj hi)]
  exact hp.separative_monotone (hf.2 i hi j hj)

theorem projectionQuotient_name_descending {Q S T U π τ ρ : V}
    {α : A.Model} [IsOrdinal α]
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) (f : ForcingName A.P)
    (hf : IsForcingDescending (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α (A.ofName f)) :
    IsForcingDescending (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α
      (A.ofName ⟨forcingCompositionName A.P A.R f.val (checkName A.one ρ),
        forcingCompositionName_isName _ _ _ _⟩) := by
  rw [A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName A.top.1 ρ⟩]
  exact A.projectionQuotient_sequence_descending hπ hτ hρ he hf

end ForcingContext
end ZFVP
