import ZFVP.ModelTheory.SplitSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingSplitProjection.separative_closedAt_base {P R Q S π E α : V} [IsOrdinal α]
    (h : IsForcingSplitProjection P R Q S π E)
    (hc : IsForcingClosedAt Q (forcingSeparativeOrder Q S) α) :
    IsForcingClosedAt P (forcingSeparativeOrder P R) α := by
  intro f hf
  have hdesc : IsForcingDescending Q (forcingSeparativeOrder Q S) α (compose f E) := by
    refine ⟨compose_function hf.1 h.maps, ?_⟩
    intro i hi j hj
    have hjα := IsOrdinal.toIsTransitive.mem_trans hj hi
    have hfi := function_value_mem hf.1 hi
    have hfj := function_value_mem hf.1 hjα
    rw [value_compose_of_mem_function hf.1 h.maps hi,
      value_compose_of_mem_function hf.1 h.maps hjα]
    apply (h.separative_below (function_value_mem h.maps hfi) hfj).mpr
    rw [h.right_inverse _ hfi]
    exact hf.2 i hi j hj
  obtain ⟨q, hq, hb⟩ := hc _ hdesc
  refine ⟨π ‘ q, function_value_mem h.projection.maps hq, ?_⟩
  intro i hi
  have hh := hb i hi
  rw [value_compose_of_mem_function hf.1 h.maps hi] at hh
  exact (h.separative_below hq (function_value_mem hf.1 hi)).mp hh

end ZFVP
