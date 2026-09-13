import ZFVP.ModelTheory.ForcingIsomorphismFormula
import ZFVP.SetTheory.CompositionLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIsomorphism.comp {P R Q S A B f g : V}
    (hf : IsForcingIsomorphism P R Q S f) (hg : IsForcingIsomorphism Q S A B g) :
    IsForcingIsomorphism P R A B (compose f g) := by
  let := IsFunction.of_mem hf.1
  let := IsFunction.of_mem hg.1
  have hc := compose_function hf.1 hg.1
  refine ⟨hc, compose_injective hf.2.1 hg.2.1, ?_, ?_⟩
  · apply subset_antisymm (range_subset_of_mem_function hc)
    intro a ha
    obtain ⟨q, hq, hqa⟩ := hg.surjective a ha
    obtain ⟨p, hp, hpq⟩ := hf.surjective q hq
    have he : (compose f g) ‘ p = a := by
      rw [value_compose_of_mem_function hf.1 hg.1 hp, hpq, hqa]
    exact he ▸ value_mem_range hc hp
  · intro p hp q hq
    rw [value_compose_of_mem_function hf.1 hg.1 hp, value_compose_of_mem_function hf.1 hg.1 hq]
    exact (hf.2.2.2 p hp q hq).trans
      (hg.2.2.2 _ (function_value_mem hf.1 hp) _ (function_value_mem hf.1 hq))

end ZFVP
