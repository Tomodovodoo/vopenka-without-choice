import ZFVP.SetTheory.ForcingDirectedClosure
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingDirectedFamily.map {P R Q S I f u : V}
    (hf : IsForcingDirectedFamily P R I f) (hu : u ∈ Q ^ P)
    (hmono : ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → ⟨u ‘ p, u ‘ q⟩ₖ ∈ S) :
    IsForcingDirectedFamily Q S I (compose f u) := by
  refine ⟨compose_function hf.1 hu, ?_⟩
  intro i hi j hj
  obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
  refine ⟨k, hk, ?_, ?_⟩
  · rw [value_compose_of_mem_function hf.1 hu hk, value_compose_of_mem_function hf.1 hu hi]
    exact hmono _ (function_value_mem hf.1 hk) _ (function_value_mem hf.1 hi) hki
  · rw [value_compose_of_mem_function hf.1 hu hk, value_compose_of_mem_function hf.1 hu hj]
    exact hmono _ (function_value_mem hf.1 hk) _ (function_value_mem hf.1 hj) hkj

theorem forcingFamilyBound_map {P R Q S I f u p : V}
    (hf : f ∈ P ^ I) (hu : u ∈ Q ^ P) (hp : p ∈ P)
    (hmono : ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → ⟨u ‘ p, u ‘ q⟩ₖ ∈ S)
    (hb : ∀ i ∈ I, ⟨p, f ‘ i⟩ₖ ∈ R) :
    ∀ i ∈ I, ⟨u ‘ p, (compose f u) ‘ i⟩ₖ ∈ S := by
  intro i hi
  rw [value_compose_of_mem_function hf hu hi]
  exact hmono p hp _ (function_value_mem hf hi) (hb i hi)

end ZFVP
