import ZFVP.ModelTheory.CodedMembershipIsomorphism
import ZFVP.SetTheory.LowenheimSkolemCardinals

/-! The range of a coded membership embedding is elementary. If the
source is transitive, its inverse graph is the transitive collapse. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f : V} (h : IsCodedMembershipEmbedding A B f)

include h

theorem range_nonempty : IsNonempty (range f) := by
  obtain ⟨x, hx⟩ := h.source_nonempty
  exact ⟨f ‘ x, value_mem_range h.function hx⟩

theorem inverse_membership {x y : V} (hx : x ∈ range f) (hy : y ∈ range f) :
    (converseGraph f) ‘ x ∈ (converseGraph f) ‘ y ↔ x ∈ y := by
  have hg := converseGraph_mem_function h.function h.injective
  have he := h.value_mem_iff (function_value_mem hg hx) (function_value_mem hg hy)
  rw [value_converseGraph_value h.function h.injective hx,
    value_converseGraph_value h.function h.injective hy] at he
  exact he.symm

theorem inverse_elementary : IsCodedMembershipEmbedding (range f) A (converseGraph f) := by
  let := IsFunction.of_mem h.function
  apply codedMembershipEmbedding_of_isomorphism h.range_nonempty
    (converseGraph_mem_function h.function h.injective) (converseGraph_injective f)
    (by rw [range_converseGraph, domain_eq_of_mem_function h.function])
  exact fun _ hx _ hy ↦ h.inverse_membership hx hy

theorem range_elementary : IsElementaryInclusion (range f) B := by
  have hh := h.inverse_elementary.comp h
  have he : compose (converseGraph f) f = SetTheory.identity (range f) := by
    have hhf := compose_function (converseGraph_mem_function h.function h.injective) h.function
    let := IsFunction.of_mem hhf
    apply functions_eq_of_domain_values
      (by rw [domain_eq_of_mem_function hhf, domain_eq_of_mem_function (identity_mem_function (range f))])
    intro y hy
    rw [domain_eq_of_mem_function hhf] at hy
    rw [value_compose_of_mem_function (converseGraph_mem_function h.function h.injective) h.function hy,
      value_converseGraph_value h.function h.injective hy]
    exact (value_eq_of_kpair_mem (f := SetTheory.identity (range f)) (by simp [hy])).symm
  rwa [he] at hh

theorem range_collapse [IsTransitive A] :
    IsTransitiveCollapse (membershipRelation (range f)) (range f) A (converseGraph f) := by
  let := IsFunction.of_mem h.function
  have hg := converseGraph_mem_function h.function h.injective
  refine ⟨inferInstance, hg, ?_, ?_, ?_⟩
  · rw [range_converseGraph, domain_eq_of_mem_function h.function]
  · intro x hx y hy he
    exact injective_value_eq hg (converseGraph_injective f) hx hy he
  · intro x hx y hy
    rw [h.inverse_membership hx hy]
    simp [membershipRelation, hx, hy]

theorem range_smallCollapse {κ : V} [IsOrdinal κ] [IsTransitive A]
    (hA : A ∈ hierarchy κ) : HasSmallTransitiveCollapse κ (range f) :=
  ⟨A, hA, converseGraph f, h.range_collapse⟩

end IsCodedMembershipEmbedding

end ZFVP
