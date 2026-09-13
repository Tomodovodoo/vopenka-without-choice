import ZFVP.ModelTheory.CohenSupportedValues
import ZFVP.ModelTheory.CohenEnumerationInverse
import ZFVP.SetTheory.DedekindFinite

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem cohen_reals_no_omega_injection {G : Set V}
    (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    ¬(ω : (cohenContext (ω : V) G hG).Model) ≤# CohenModel.reals hG := by
  let S := cohenContext (ω : V) G hG
  rintro ⟨f, hf, hfi⟩
  obtain ⟨τ, rfl⟩ := S.ofName_surjective f
  have hfun : IsFunction (S.ofName τ) := IsFunction.of_mem hf
  obtain ⟨E, hEω, hEf, hE⟩ := cohenName_finiteSupport τ.property
  apply CohenModel.no_injection_with_finite_indices hG hEf hf hfi
  intro n hn
  have hnc : S.check n ∈ (ω : S.Model) := by
    rw [← S.checkEmbedding.map_omega]
    exact (S.check_mem_iff n ω).mpr hn
  obtain ⟨i, hi, hval⟩ := (CohenModel.mem_reals_iff hG _).mp (function_value_mem hf hnc)
  exact ⟨i, hi, CohenModel.function_value_supported hG τ hEω hEf hE hfun hi hval, hval⟩

theorem cohen_reals_dedekindFinite {G : Set V}
    (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    IsInternallyDedekindFinite (CohenModel.reals hG) :=
  (dedekindFinite_iff_no_omega_injection _).mpr (cohen_reals_no_omega_injection hG)

theorem cohen_model_not_choice {G : Set V}
    (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    ¬InternalChoice (cohenContext (ω : V) G hG).Model :=
  not_internalChoice_of_infinite_dedekindFinite (cohen_reals_internallyInfinite hG) (cohen_reals_dedekindFinite hG)

theorem cohen_model_not_dependentChoice {G : Set V}
    (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    ¬InternalDependentChoice (cohenContext (ω : V) G hG).Model :=
  not_dependentChoice_of_infinite_dedekindFinite (cohen_reals_internallyInfinite hG) (cohen_reals_dedekindFinite hG)

end ZFVP
