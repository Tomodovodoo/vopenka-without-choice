import ZFVP.ModelTheory.ForcingReflectingProjection
import ZFVP.ModelTheory.ForcingProjectionComposition
import ZFVP.ModelTheory.ForcingIsomorphismFormula
import ZFVP.SetTheory.EquivalentRetractionForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R N T Q S n f : V}

theorem IsForcingRetraction.isomorphism_right_inverse
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    {q : V} (hq : q ∈ Q) : (compose n f) ‘ ((converseGraph f) ‘ q) = q := by
  have hp := function_value_mem hf.inverse_maps hq
  rw [value_compose_of_mem_function hr.maps hf.1 (hr.inclusion _ hp), hr.fixes _ hp, hf.value_inverse hq]

theorem IsForcingRetraction.isomorphism_left_inverse
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    {p : V} (hp : p ∈ P) : (converseGraph f) ‘ ((compose n f) ‘ p) = n ‘ p := by
  rw [value_compose_of_mem_function hr.maps hf.1 hp, hf.inverse_value (function_value_mem hr.maps hp)]

theorem IsForcingRetraction.isomorphism_surjective
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f) :
    ∀ q ∈ Q, ∃ p ∈ P, (compose n f) ‘ p = q := by
  intro q hq
  exact ⟨(converseGraph f) ‘ q, hr.inclusion _ (function_value_mem hf.inverse_maps hq), hr.isomorphism_right_inverse hf hq⟩

theorem IsForcingRetraction.isomorphism_order_iff
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    (hR : IsForcingPreorder P R) (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    {p q : V} (hp : p ∈ P) (hq : q ∈ P) :
    ⟨p, q⟩ₖ ∈ R ↔ ⟨(compose n f) ‘ p, (compose n f) ‘ q⟩ₖ ∈ S := by
  rw [value_compose_of_mem_function hr.maps hf.1 hp, value_compose_of_mem_function hr.maps hf.1 hq,
    ← hf.2.2.2 _ (function_value_mem hr.maps hp) _ (function_value_mem hr.maps hq)]
  constructor
  · exact hr.monotone p hp q hq
  · intro h
    exact hR.2.2 p hp _ (hr.inclusion _ (function_value_mem hr.maps hq)) q hq
      ((hr.below p hp _ (function_value_mem hr.maps hq)).mpr h) (he q hq)

theorem IsForcingRetraction.isomorphism_projection
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f) :
    IsForcingProjection Q S P R (compose n f) := hf.projection.comp hr.projection

theorem IsForcingRetraction.isomorphism_generic_member_iff
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    {G : Set V} (hG : IsExternalForcingFilter P R G) {p : V} (hp : p ∈ P) :
    (compose n f) ‘ p ∈ forcingProjectionGeneric Q S (compose n f) G ↔ p ∈ G :=
  (hr.isomorphism_projection hf).image_member_iff
    (fun _ hp _ hq ↦ (hr.isomorphism_order_iff hf hR he hp hq).mpr) hS hG hp

theorem IsForcingRetraction.isomorphism_generic_preimage
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    (hR : IsForcingPreorder P R) (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    {H : Set V} (hH : IsExternalForcingGeneric Q S H) :
    IsExternalForcingGeneric P R (forcingProjectionPreimage P (compose n f) H) :=
  (hr.isomorphism_projection hf).preimage_generic
    (fun _ hp _ hq ↦ (hr.isomorphism_order_iff hf hR he hp hq).mpr)
    (hr.isomorphism_surjective hf) hH

theorem IsForcingRetraction.isomorphism_forcingFormula_iff
    (hr : IsForcingRetraction N T P R n) (hf : IsForcingIsomorphism N T Q S f)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T) (hS : IsForcingPreorder Q S)
    (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R ∧ ⟨p, n ‘ p⟩ₖ ∈ R)
    {k : ℕ} (φ : SetTheorySemisentence k) (v : Fin k → V) (hv : ∀ i, IsForcingName P (v i))
    {p : V} (hp : p ∈ P) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      (compose n f) ‘ p ∈ forcingFormula Q S φ (standardTuple (fun i ↦ nameAction (compose n f) (v i))) := by
  rw [hr.forcingFormula_nameAction_iff hR hT he φ v hv hp,
    value_compose_of_mem_function hr.maps hf.1 hp]
  have hn : ∀ i, IsForcingName N (nameAction n (v i)) := fun i ↦ nameAction_isName hr.maps (hv i)
  have heq : (fun i ↦ nameAction (compose n f) (v i)) = (fun i ↦ nameAction f (nameAction n (v i))) := by
    funext i
    exact (nameAction_compose hr.maps hf.1 (hv i)).symm
  rw [heq]
  exact (forcingFormula_isomorphism_iff hT hS hf φ _ hn (function_value_mem hr.maps hp)).symm

end ZFVP
