import ZFVP.ModelTheory.UsubaRestorationClosure
import ZFVP.ModelTheory.TwoStepSelectedDescending

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel
variable (A : ForcingContext V)
local notation "Q" => usubaSaturatedPosetName A.P A.R
local notation "S" => reverseInclusionOrderName A.P A.R Q
local notation "h" => usubaSaturated_iterand A.order A.top

theorem selected_usuba_union_bound
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
      (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q ∅)
          (twoStepOrder A.P A.R Q S ∅) (twoStepProjection A.P A.R Q ∅))) α (A.ofName f))
    (hDC : InternalDependentChoiceAt α) :
    let u := A.ofName ⟨forcingSelectedUnion A.P A.R A.one (twoStepNames Q ∅) (twoStepTailSelector A.P A.R Q ∅) f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩
    u ∈ (usubaRestorationPoset : A.Model) ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check (twoStepTailSelector A.P A.R Q ∅)))
        (A.evaluationGraph (twoStepNames Q ∅) (fun _ hτ ↦ (h).name hτ))) ‘ i⟩ₖ ∈ reverseInclusionOrder (usubaRestorationPoset : A.Model) := by
  have hs := selected_tail_descending A h hf
  have hQ : A.ofName ⟨Q, (h).posetName⟩ = (usubaRestorationPoset : A.Model) :=
    A.usubaSaturatedName_value
  have hS : A.ofName ⟨S, (h).orderName⟩ = reverseInclusionOrder (usubaRestorationPoset : A.Model) :=
    (A.reverseOrderName_value A.usubaSaturatedName).trans (congrArg reverseInclusionOrder hQ)
  rw [hQ, hS] at hs
  exact A.forcingSelectedUnion_usuba_bound (fun _ hτ ↦ (h).name hτ)
    (twoStepTailSelector_maps A.P A.R Q ∅) f
    (mem_function_of_mem_function_of_subset hf.1 sep_subset) hDC hs

theorem local_usuba_union_bound {p : V} (hp : p ∈ A.G)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
      (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q ∅)
          (twoStepOrder A.P A.R Q S ∅) (twoStepProjection A.P A.R Q ∅))) α (A.ofName f))
    (hDC : InternalDependentChoiceAt α) :
    let ν := forcingCarrierLocalNormalize A.P A.R (usubaRestorationPosetName A.P A.R) p
      (forcingSelectedUnion A.P A.R A.one (twoStepNames Q ∅) (twoStepTailSelector A.P A.R Q ∅) f.val)
    let u := A.ofName ⟨ν, forcingCarrierLocalNormalize_isName _ _ _ _ _⟩
    u ∈ A.ofName ⟨Q, (h).posetName⟩ ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check (twoStepTailSelector A.P A.R Q ∅)))
        (A.evaluationGraph (twoStepNames Q ∅) (fun _ hτ ↦ (h).name hτ))) ‘ i⟩ₖ ∈ A.ofName ⟨S, (h).orderName⟩ := by
  have hb := selected_usuba_union_bound A f hf hDC
  let τ : ForcingName A.P := ⟨forcingSelectedUnion A.P A.R A.one (twoStepNames Q ∅) (twoStepTailSelector A.P A.R Q ∅) f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩
  have hm : A.ofName τ ∈ A.ofName A.usubaRestorationName := by
    rw [A.usubaRestorationName_value]
    exact hb.1
  have he := A.carrierLocalNormalize_value A.usubaRestorationName τ hp hm
  have hQ : A.ofName ⟨Q, (h).posetName⟩ = (usubaRestorationPoset : A.Model) :=
    A.usubaSaturatedName_value
  have hS : A.ofName ⟨S, (h).orderName⟩ = reverseInclusionOrder (usubaRestorationPoset : A.Model) :=
    (A.reverseOrderName_value A.usubaSaturatedName).trans (congrArg reverseInclusionOrder hQ)
  dsimp only [ForcingContext.usubaRestorationName, τ] at he
  dsimp only
  rw [he, hQ, hS]
  exact hb

theorem mem_of_local_usuba_union {p q : V} (hp : p ∈ A.G)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
      (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q ∅) (twoStepProjection A.P A.R Q ∅))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q ∅)
          (twoStepOrder A.P A.R Q S ∅) (twoStepProjection A.P A.R Q ∅))) α (A.ofName f))
    (hDC : InternalDependentChoiceAt α)
    {G : Set V} (hG : IsExternalForcingGeneric
      (twoStepConditions A.P A.R Q ∅) (twoStepOrder A.P A.R Q S ∅) G)
    (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q ∅) G)
    (hq : ⟨q, forcingCarrierLocalNormalize A.P A.R (usubaRestorationPosetName A.P A.R) p
      (forcingSelectedUnion A.P A.R A.one (twoStepNames Q ∅) (twoStepTailSelector A.P A.R Q ∅) f.val)⟩ₖ ∈ G) :
    ∀ i ∈ α, (A.ofName f) ‘ i ∈ A.projectionQuotientFilter G := by
  apply mem_of_selected_tail_bound A h hG hA
    ⟨_, forcingCarrierLocalNormalize_isName _ _ _ _ _⟩ hq
    (mem_function_of_mem_function_of_subset hf.1 sep_subset)
  · intro i hi c hc he
    have hcQ := he ▸ function_value_mem hf.1 hi
    have hcG := ((A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q ∅)).mp hcQ).2
    rwa [twoStepProjection_value hc] at hcG
  · exact (local_usuba_union_bound A hp f hf hDC).2

end TwoStepModel
end ZFVP
