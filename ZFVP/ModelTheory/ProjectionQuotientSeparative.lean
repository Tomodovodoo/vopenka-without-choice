import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.SetTheory.ForcingSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Ground separative comparisons remain valid inside the actual quotient.
The generic meets the projections of the common extensions. -/
theorem projectionQuotient_separative_of_ground (A : ForcingContext V) {Q S π q r : V}
    (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (hq : A.check q ∈ A.projectionQuotient Q π)
    (hr : A.check r ∈ A.projectionQuotient Q π)
    (hqr : ⟨q, r⟩ₖ ∈ forcingSeparativeOrder Q S) :
    ⟨A.check q, A.check r⟩ₖ ∈ forcingSeparativeOrder
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
  refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr ⟨hq, hr, ?_⟩
  intro x hx hxq
  obtain ⟨s, hs, hsG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
  have hsq := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxq).1
  rw [← A.check_kpair, A.check_mem_iff] at hsq
  have hqQ := ((A.check_mem_projectionQuotient_iff hπ.maps).mp hq).1
  let D : V := {p ∈ A.P ; ∃ u ∈ Q, ⟨u, s⟩ₖ ∈ S ∧ ⟨u, r⟩ₖ ∈ S ∧ π ‘ u = p}
  have hd : ForcingDenseBelow A.P A.R D (π ‘ s) := by
    refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
    intro p hp hps
    obtain ⟨t, ht, hts, het⟩ := hπ.lift s hs p hp hps
    obtain ⟨u, hu, hut, hur⟩ := ((kpair_mem_forcingSeparativeOrder Q S q r).mp hqr).2.2
      t ht (hS.2.2 t ht s hs q hqQ hts hsq)
    refine ⟨π ‘ u, mem_sep_iff.mpr ⟨function_value_mem hπ.maps hu,
      u, hu, hS.2.2 u hu t ht s hs hut hts, hur, rfl⟩, ?_⟩
    exact het ▸ hπ.monotone u hu t ht hut
  obtain ⟨p, hpG, hpD⟩ := externalForcingGeneric_meets_denseBelow A.order A.generic hsG hd
  obtain ⟨u, hu, hus, hur, heu⟩ := (mem_sep_iff.mp hpD).2
  have hu' := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hu, heu.symm ▸ hpG⟩
  refine ⟨A.check u, hu', ?_, ?_⟩
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair u s ▸ (A.check_mem_iff _ _).mpr hus, hu', hx⟩
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair u r ▸ (A.check_mem_iff _ _).mpr hur, hu', hr⟩

end ForcingContext
end ZFVP
