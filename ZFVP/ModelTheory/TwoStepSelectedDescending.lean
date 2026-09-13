import ZFVP.ModelTheory.TwoStepSelectedUnion
import ZFVP.ModelTheory.TwoStepQuotientProjection
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)

theorem selected_tail_sequence_eq {α f : A.Model}
    (hf : f ∈ A.projectionQuotient (twoStepConditions A.P A.R Q t)
      (twoStepProjection A.P A.R Q t) ^ α) :
    compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
      (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ)) =
        compose f (A.twoStepQuotientProjection h) := by
  have hfcheck := mem_function_of_mem_function_of_subset hf sep_subset
  have hselector := (A.check_function_iff (twoStepTailSelector A.P A.R Q t)
    (twoStepConditions A.P A.R Q t) (twoStepNames Q t)).mpr
      (twoStepTailSelector_maps A.P A.R Q t)
  have hl := compose_function (compose_function hfcheck hselector)
    (A.evaluationGraph_mem_function (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))
  have hr := compose_function hf (A.twoStepQuotientProjection_projection h).maps
  let := IsFunction.of_mem hl
  let := IsFunction.of_mem hr
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hl, domain_eq_of_mem_function hr]
  · intro i hi
    have hiα : i ∈ α := (domain_eq_of_mem_function hl) ▸ hi
    obtain ⟨c, hc, hcg, he⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) _).mp (function_value_mem hf hiα)
    obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    have hp : p ∈ A.G := by simpa only [twoStepProjection_value hc, kpair.π₁_kpair] using hcg
    have hlv : (compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) ‘ i =
          A.ofName ⟨τ, h.name hτ⟩ := by
      simpa only [kpair.π₂_kpair] using selected_tail_value A h hc hfcheck hiα he
    rw [hlv,
      value_compose_of_mem_function hf (A.twoStepQuotientProjection_projection h).maps hiα, he,
      A.twoStepQuotientProjection_value h ⟨τ, h.name hτ⟩ hc hp]

theorem selected_tail_descending {α f : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α f) :
    IsForcingDescending (A.ofName ⟨Q, h.posetName⟩)
      (forcingSeparativeOrder (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)) α
      (compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) := by
  rw [selected_tail_sequence_eq A h hf.1]
  have hπ := A.twoStepQuotientProjection_projection h
  refine ⟨compose_function hf.1 hπ.maps, ?_⟩
  intro i hi j hj
  rw [value_compose_of_mem_function hf.1 hπ.maps hi,
    value_compose_of_mem_function hf.1 hπ.maps (IsOrdinal.toIsTransitive.mem_trans hj hi)]
  exact hπ.separative_monotone (hf.2 i hi j hj)

end TwoStepModel
end ZFVP
