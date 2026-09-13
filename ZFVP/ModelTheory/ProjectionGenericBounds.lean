import ZFVP.ModelTheory.QuotientGenericCriterion
import ZFVP.ModelTheory.ProjectionNameTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem projectionInclusion_mem_generic_iff (A B : ForcingContext V) {π E : V}
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G)
    {x : A.Model} (hx : x ∈ A.check B.P) :
    A.projectionInclusion B hπ he x ∈ B.genericSet ↔ x ∈ A.projectionQuotientFilter B.G := by
  obtain ⟨q, _, rfl⟩ := (A.mem_check_iff B.P x).mp hx
  rw [A.projectionInclusion_check B hπ he, B.check_mem_genericSet_iff]
  constructor
  · exact fun hq ↦ ⟨q, hq, rfl⟩
  · rintro ⟨r, hr, hqr⟩
    exact ((A.check_eq_iff q r).mp hqr) ▸ hr

theorem projectionInclusion_sequence_in_generic (A B : ForcingContext V) {π E q : V}
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) (hq : q ∈ B.G)
    {α f : A.Model} (hf : f ∈ A.projectionQuotient B.P π ^ α)
    (hb : ∀ i ∈ α, ⟨A.check q, f ‘ i⟩ₖ ∈ forcingSeparativeOrder
      (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) :
    ∀ j ∈ A.projectionInclusion B hπ he α,
      (A.projectionInclusion B hπ he f) ‘ j ∈ B.genericSet := by
  rw [(A.projectionInclusion B hπ he).forall_mem_iff]
  intro i hi
  rw [← (A.projectionInclusion B hπ he).map_value_total]
  apply (A.projectionInclusion_mem_generic_iff B hπ he
    (mem_sep_iff.mp (function_value_mem hf hi)).1).mpr
  exact externalForcingGeneric_separative_upward
    (A.projectionQuotient_preorder hπ.projection.maps B.order)
    (A.projectionQuotient_generic hπ B.order B.generic he) ⟨q, hq, rfl⟩ (hb i hi)

theorem projectionQuotient_bound_of_generic_sequences (A : ForcingContext V) [Countable A.Model]
    {Q S π E t q : V} (hS : IsForcingPreorder Q S) (ht : IsForcingTop Q S t)
    (hπ : IsForcingSplitProjection A.P A.R Q S π E)
    (hq : A.check q ∈ A.projectionQuotient Q π)
    {α f : A.Model} (hf : f ∈ A.projectionQuotient Q π ^ α)
    (h : ∀ (G : Set V) (hG : IsExternalForcingGeneric Q S G)
      (he : forcingProjectionGeneric A.P A.R π G = A.G), q ∈ G →
      let B : ForcingContext V := ⟨Q, S, t, G, hS, ht, hG⟩
      ∀ j ∈ A.projectionInclusion B hπ he α,
        (A.projectionInclusion B hπ he f) ‘ j ∈ B.genericSet) :
    ∀ i ∈ α, ⟨A.check q, f ‘ i⟩ₖ ∈ forcingSeparativeOrder
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
  intro i hi
  apply A.projectionQuotient_separative_of_all_generics hπ.projection hS hq (function_value_mem hf hi)
  intro G hG he hqG
  let B : ForcingContext V := ⟨Q, S, t, G, hS, ht, hG⟩
  have hv := h G hG he hqG (A.projectionInclusion B hπ he i)
    (((A.projectionInclusion B hπ he).mem_iff i α).mpr hi)
  rw [← (A.projectionInclusion B hπ he).map_value_total] at hv
  exact (A.projectionInclusion_mem_generic_iff B hπ he
    (mem_sep_iff.mp (function_value_mem hf hi)).1).mp hv

end ForcingContext
end ZFVP
