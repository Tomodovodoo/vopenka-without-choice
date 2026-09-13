import ZFVP.ModelTheory.ForcingProjection
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingProjection.comp {P R Q S U T π ρ : V}
    (hπ : IsForcingProjection P R Q S π) (hρ : IsForcingProjection Q S U T ρ) :
    IsForcingProjection P R U T (compose ρ π) := by
  have hv (a : V) (ha : a ∈ U) := value_compose_of_mem_function hρ.maps hπ.maps ha
  refine ⟨compose_function hρ.maps hπ.maps, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hv a ha, hv b hb]
    exact hπ.monotone _ (function_value_mem hρ.maps ha) _ (function_value_mem hρ.maps hb)
      (hρ.monotone a ha b hb hab)
  · intro a ha p hp hpa
    rw [hv a ha] at hpa
    obtain ⟨q, hq, hqa, hqp⟩ := hπ.lift _ (function_value_mem hρ.maps ha) p hp hpa
    obtain ⟨b, hb, hba, hbq⟩ := hρ.lift a ha q hq hqa
    exact ⟨b, hb, hba, by rw [hv b hb, hbq, hqp]⟩

theorem forcingProjectionGeneric_comp {P R Q S U T π ρ : V}
    (hπ : IsForcingProjection P R Q S π) (hρ : IsForcingProjection Q S U T ρ)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S) {G : Set V}
    (hG : IsExternalForcingFilter U T G) :
    forcingProjectionGeneric P R π (forcingProjectionGeneric Q S ρ G) =
      forcingProjectionGeneric P R (compose ρ π) G := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨hp, q, ⟨hq, a, haG, haq⟩, hqp⟩
    have ha := hG.1 a haG
    refine ⟨hp, a, haG, ?_⟩
    rw [value_compose_of_mem_function hρ.maps hπ.maps ha]
    exact hR.2.2 _ (function_value_mem hπ.maps (function_value_mem hρ.maps ha))
      _ (function_value_mem hπ.maps hq) p hp
      (hπ.monotone _ (function_value_mem hρ.maps ha) q hq haq) hqp
  · rintro ⟨hp, a, haG, hap⟩
    rw [value_compose_of_mem_function hρ.maps hπ.maps (hG.1 a haG)] at hap
    exact ⟨hp, ρ ‘ a, hρ.image_mem hS hG haG, hap⟩

end ZFVP
