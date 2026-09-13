import ZFVP.SetTheory.ForcingSaturatedName
import ZFVP.SetTheory.AtomicForcingSubstitution

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSaturatedName_atomicEquality {P R U Q p : V}
    (hR : IsForcingPreorder P R) (hQ : IsForcingName P Q)
    (hU : domain Q ⊆ U) (hp : p ∈ P) :
    p ∈ atomicEquality P R (forcingSaturatedName P R U Q) Q := by
  apply (atomicEquality_iff_membership _ _ _ _ _ hR).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro τ s hs q hq _ hqs
    have hh := (pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hs
    exact atomicMembership_mono hR hh.2.2.2 hq hqs
  · intro τ s hs q hq _ hqs
    have hτ : IsForcingName P τ := forcingName_subname hQ hs
    have hsP := forcingName_condition hQ hs
    exact forcingSaturatedName_forces_member hR (hU _ (mem_domain_of_kpair_mem hs)) hq hτ
      (atomicMembership_mono hR (atomicMembership_of_pair hR hsP hs) hq hqs)

theorem forcingSaturatedName_eq_of_forced_equality {P R U N N' : V}
    (hR : IsForcingPreorder P R)
    (he : ∀ p ∈ P, p ∈ atomicEquality P R N N') :
    forcingSaturatedName P R U N = forcingSaturatedName P R U N' := by
  apply mem_ext
  intro z
  by_cases hz : z ∈ U ×ˢ P
  · obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp hz
    simp only [pair_mem_forcingSaturatedName]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr Iff.rfl (atomicEquality_membership_iff hR (he p hp) τ).2))
  · exact iff_of_false (fun h ↦ hz (forcingSaturatedName_subset _ _ _ _ _ h))
      (fun h ↦ hz (forcingSaturatedName_subset _ _ _ _ _ h))

end ZFVP
