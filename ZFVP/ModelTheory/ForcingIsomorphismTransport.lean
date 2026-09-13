import ZFVP.SetTheory.ForcingIsomorphism
import ZFVP.SetTheory.NameAction
import ZFVP.SetTheory.NameActionClosure
import ZFVP.SetTheory.FunctionUnion
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsForcingIsomorphism
variable {P R Q S f : V} (h : IsForcingIsomorphism P R Q S f)
include h

theorem inverse_maps : converseGraph f ∈ P ^ Q := by
  simpa only [h.2.2.1] using converseGraph_mem_function h.1 h.2.1

theorem inverse_value {p : V} (hp : p ∈ P) : (converseGraph f) ‘ (f ‘ p) = p :=
  converseGraph_value_value h.1 h.2.1 hp

theorem value_inverse {q : V} (hq : q ∈ Q) : f ‘ ((converseGraph f) ‘ q) = q :=
  value_converseGraph_value h.1 h.2.1 (h.2.2.1.symm ▸ hq)

theorem inverse : IsForcingIsomorphism Q S P R (converseGraph f) := by
  let := IsFunction.of_mem h.1
  refine ⟨h.inverse_maps, converseGraph_injective f,
    (range_converseGraph f).trans (domain_eq_of_mem_function h.1), ?_⟩
  intro p hp q hq
  have hh := h.2.2.2 _ (function_value_mem h.inverse_maps hp) _ (function_value_mem h.inverse_maps hq)
  simpa only [h.value_inverse hp, h.value_inverse hq] using hh.symm

theorem compose_inverse : compose f (converseGraph f) = identity P := by
  have hc := compose_function h.1 h.inverse_maps
  let := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc]
    exact (domain_eq_of_mem_function (identity_mem_function P)).symm
  · intro p hp
    rw [domain_eq_of_mem_function hc] at hp
    rw [value_compose_of_mem_function h.1 h.inverse_maps hp, h.inverse_value hp, identity_value hp]

theorem inverse_compose : compose (converseGraph f) f = identity Q := by
  have hc := compose_function h.inverse_maps h.1
  let := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc]
    exact (domain_eq_of_mem_function (identity_mem_function Q)).symm
  · intro q hq
    rw [domain_eq_of_mem_function hc] at hq
    rw [value_compose_of_mem_function h.inverse_maps h.1 hq, h.value_inverse hq, identity_value hq]

theorem name_inverse_cancel {τ : V} (hτ : IsForcingName P τ) :
    nameAction (converseGraph f) (nameAction f τ) = τ := by
  rw [nameAction_compose h.1 h.inverse_maps hτ, h.compose_inverse, nameAction_identity hτ]

theorem name_cancel_inverse {τ : V} (hτ : IsForcingName Q τ) :
    nameAction f (nameAction (converseGraph f) τ) = τ := by
  rw [nameAction_compose h.inverse_maps h.1 hτ, h.inverse_compose, nameAction_identity hτ]

theorem splitProjection : IsForcingSplitProjection P R Q S (converseGraph f) f := by
  refine ⟨⟨h.inverse_maps, ?_, ?_⟩, h.1, fun _ hp ↦ h.inverse_value hp, ?_⟩
  · intro p hp q hq hpq
    exact (h.inverse.2.2.2 p hp q hq).mp hpq
  · intro q hq p hp hpq
    refine ⟨f ‘ p, function_value_mem h.1 hp, ?_, h.inverse_value hp⟩
    have hh := (h.2.2.2 p hp _ (function_value_mem h.inverse_maps hq)).mp hpq
    simpa only [h.value_inverse hq] using hh
  · intro q hq p hp
    have hh := h.2.2.2 _ (function_value_mem h.inverse_maps hq) p hp
    simpa only [h.value_inverse hq] using hh.symm

theorem projection : IsForcingProjection Q S P R f := by
  refine ⟨h.1, fun p hp q hq hpq ↦ (h.2.2.2 p hp q hq).mp hpq, ?_⟩
  intro p hp q hq hqp
  refine ⟨(converseGraph f) ‘ q, function_value_mem h.inverse_maps hq, ?_, h.value_inverse hq⟩
  apply (h.2.2.2 _ (function_value_mem h.inverse_maps hq) p hp).mpr
  simpa only [h.value_inverse hq] using hqp

theorem generic_image_iff {G : Set V} (hG : IsExternalForcingFilter P R G)
    (hS : IsForcingPreorder Q S) {q : V} (hq : q ∈ Q) :
    q ∈ forcingProjectionGeneric Q S f G ↔ (converseGraph f) ‘ q ∈ G := by
  constructor
  · rintro ⟨_, p, hp, hpq⟩
    apply hG.2.2.1 p hp _ (function_value_mem h.inverse_maps hq)
    have hh := (h.inverse.2.2.2 _ (function_value_mem h.1 (hG.1 p hp)) q hq).mp hpq
    simpa only [h.inverse_value (hG.1 p hp)] using hh
  · intro hqg
    refine ⟨hq, (converseGraph f) ‘ q, hqg, ?_⟩
    rw [h.value_inverse hq]
    exact hS.2.1 q hq

theorem generic_inverse_image {G : Set V} (hG : IsExternalForcingFilter P R G)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S) :
    forcingProjectionGeneric P R (converseGraph f) (forcingProjectionGeneric Q S f G) = G := by
  ext p
  constructor
  · intro hp
    have hpP := hp.1
    have hh := (h.splitProjection.generic_iff_section hR (h.projection.filter hS hG) hpP).mp hp
    have hi := (h.generic_image_iff hG hS (function_value_mem h.1 hpP)).mp hh
    simpa only [h.inverse_value hpP] using hi
  · intro hp
    have hpP := hG.1 p hp
    apply (h.splitProjection.generic_iff_section hR (h.projection.filter hS hG) hpP).mpr
    apply (h.generic_image_iff hG hS (function_value_mem h.1 hpP)).mpr
    simpa only [h.inverse_value hpP] using hp

theorem map_top {one : V} (ht : IsForcingTop P R one) : IsForcingTop Q S (f ‘ one) := by
  refine ⟨function_value_mem h.1 ht.1, ?_⟩
  intro q hq
  have hh := (h.2.2.2 _ (function_value_mem h.inverse_maps hq) one ht.1).mp
    (ht.2 _ (function_value_mem h.inverse_maps hq))
  simpa only [h.value_inverse hq] using hh

end IsForcingIsomorphism

theorem nameAction_checkName_map {P one f : V} (hone : one ∈ P) (x : V) :
    nameAction f (checkName one x) = checkName (f ‘ one) x := by
  apply set_induction (fun x ↦ nameAction f (checkName one x) = checkName (f ‘ one) x)
    (by definability) ?_ x
  intro x ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameAction_iff (checkName_isName hone x), mem_checkName_iff]
  constructor
  · rintro ⟨σ, p, hp, hz⟩
    obtain ⟨y, hy, he⟩ := (mem_checkName_iff one x _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨y, hy, by simpa only [ih y hy] using hz⟩
  · rintro ⟨y, hy, hz⟩
    refine ⟨checkName one y, one, (mem_checkName_iff one x _).mpr ⟨y, hy, rfl⟩, ?_⟩
    simpa only [ih y hy] using hz

end ZFVP
