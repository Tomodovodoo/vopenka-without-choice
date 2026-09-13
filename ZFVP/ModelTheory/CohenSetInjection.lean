import ZFVP.ModelTheory.CohenFiniteFiberPresentation
import ZFVP.ModelTheory.CohenOrbitEnumerations
import ZFVP.ModelTheory.CohenInfiniteSet
import ZFVP.SetTheory.FiniteFiberInjection
import ZFVP.SetTheory.EndExtensionWellOrdering

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Every set of the Cohen symmetric model injects into an ordinal times the finite
sequences of Cohen reals. Ground choice is used for labels and finite enumerations. -/
theorem set_injection_ordinal_finiteSequences (hAC : InternalChoice V)
    (X : (cohenContext (ω : V) G hG).Model) :
    ∃ α : (cohenContext (ω : V) G hG).Model,
      IsOrdinal α ∧ X ≤# α ×ˢ finiteSequences (reals hG) := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨τ, rfl⟩ := S.ofName_surjective X
  obtain ⟨D, hD, hfibers⟩ := exists_finite_fiber_orbit_family hG τ
  let H := orbitFamily hG D hD
  have hdom : domain H = S.check D := domain_eq_of_mem_function (orbitFamily_mem_function hG D hD)
  have hWO := S.checkEmbedding.map_wellOrderable (wellOrderable_of_internalChoice hAC D)
  obtain ⟨α, hα, f, hf, hfi⟩ := (wellOrderable_iff_cardLE_ordinal (S.check D)).mp hWO
  obtain ⟨e, he⟩ := cohen_orbit_enumeration_family hG hAC hD
  refine ⟨α, hα, finiteFiber_cardLE_ordinal_prod_sequences (e := e) hα (hdom.symm ▸ hf) hfi
    (reals_subset_power_omega hG) ?_ ?_ ?_ ?_⟩
  · intro j hj
    exact orbitFamily_values_are_functions hG hD (hdom ▸ hj)
  · intro x hx
    obtain ⟨j, hj, hn⟩ := (hfibers x hx).2.1
    exact ⟨j, hdom.symm ▸ hj, hn⟩
  · intro x hx j hj
    exact (hfibers x hx).2.2 j (hdom ▸ hj)
  · intro j hj
    exact he j (hdom ▸ hj)

end CohenModel

end ZFVP
