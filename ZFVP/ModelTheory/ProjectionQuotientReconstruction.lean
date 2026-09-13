import ZFVP.ModelTheory.ProjectionQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

def projectionCombinedFilter (A : ForcingContext V) (Q : V) (H : Set A.Model) : Set V :=
  {q | q ∈ Q ∧ A.check q ∈ H}

theorem projectionCombined_filter (A : ForcingContext V) {Q S π : V} {H : Set A.Model}
    (hπ : IsForcingProjection A.P A.R Q S π)
    (hH : IsExternalForcingFilter (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) H) :
    IsExternalForcingFilter Q S (A.projectionCombinedFilter Q H) := by
  refine ⟨fun _ h ↦ h.1, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hH.2.1
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp (hH.1 x hx)
    exact ⟨q, hq, hx⟩
  · intro q hq r hr hqr
    have hq' := hH.1 _ hq.2
    have hqG := ((A.check_mem_projectionQuotient_iff hπ.maps).mp hq').2
    have hrG := A.generic.1.2.2.1 _ hqG _ (function_value_mem hπ.maps hr)
      (hπ.monotone q hq.1 r hr hqr)
    have hr' := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hr, hrG⟩
    refine ⟨hr, hH.2.2.1 _ hq.2 _ hr' ?_⟩
    exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair q r ▸ (A.check_mem_iff _ _).mpr hqr, hq', hr'⟩
  · intro q hq r hr
    obtain ⟨x, hx, hxq, hxr⟩ := hH.2.2.2 _ hq.2 _ hr.2
    obtain ⟨s, hs, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp (hH.1 x hx)
    have hsq := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxq).1
    have hsr := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxr).1
    rw [← A.check_kpair, A.check_mem_iff] at hsq hsr
    exact ⟨s, ⟨hs, hx⟩, hsq, hsr⟩

theorem projectionCombined_generic (A : ForcingContext V) {Q S π : V} {H : Set A.Model}
    (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (hH : IsExternalForcingGeneric (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) H) :
    IsExternalForcingGeneric Q S (A.projectionCombinedFilter Q H) := by
  refine ⟨A.projectionCombined_filter hπ hH.1, ?_⟩
  intro D hD
  obtain ⟨x, hxH, hxD⟩ := hH.2 _ (A.projectionQuotient_ground_dense hπ hS hD)
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp (mem_sep_iff.mp hxD).1
  exact ⟨q, ⟨hq, hxH⟩, (A.check_mem_iff q D).mp (mem_sep_iff.mp hxD).2⟩

theorem projectionCombined_projection (A : ForcingContext V) {Q S π : V} {H : Set A.Model}
    (hπ : IsForcingProjection A.P A.R Q S π)
    (hH : IsExternalForcingGeneric (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) H) :
    forcingProjectionGeneric A.P A.R π (A.projectionCombinedFilter Q H) = A.G := by
  ext p
  constructor
  · rintro ⟨hp, q, hq, hqp⟩
    have hqG := ((A.check_mem_projectionQuotient_iff hπ.maps).mp (hH.1.1 _ hq.2)).2
    exact A.generic.1.2.2.1 _ hqG p hp hqp
  · intro hpG
    let D : A.Model := {x ∈ A.projectionQuotient Q π ; ⟨(A.check π) ‘ x, A.check p⟩ₖ ∈ A.check A.R}
    have hd : ForcingDense (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) D := by
      refine ⟨fun x hx ↦ (mem_sep_iff.mp hx).1, ?_⟩
      intro x hx
      obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
      obtain ⟨r, hrG, hrq, hrp⟩ := A.generic.1.2.2.2 _ hqG p hpG
      obtain ⟨s, hs, hsq, hes⟩ := hπ.lift q hq r (A.generic.1.1 r hrG) hrq
      have hs' := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hs, hes.symm ▸ hrG⟩
      refine ⟨A.check s, mem_sep_iff.mpr ⟨hs', ?_⟩, ?_⟩
      · let := IsFunction.of_mem hπ.maps
        rw [A.check_value ((domain_eq_of_mem_function hπ.maps).symm ▸ hs), hes,
          ← A.check_kpair, A.check_mem_iff]
        exact hrp
      · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
          ⟨A.check_kpair s q ▸ (A.check_mem_iff _ _).mpr hsq, hs', hx⟩
    obtain ⟨x, hxH, hxD⟩ := hH.2 D hd
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp (mem_sep_iff.mp hxD).1
    have hqp := (mem_sep_iff.mp hxD).2
    let := IsFunction.of_mem hπ.maps
    rw [A.check_value ((domain_eq_of_mem_function hπ.maps).symm ▸ hq),
      ← A.check_kpair, A.check_mem_iff] at hqp
    exact ⟨A.generic.1.1 p hpG, q, ⟨hq, hxH⟩, hqp⟩

theorem projectionCombined_quotientFilter (A : ForcingContext V) {Q S π : V} {H : Set A.Model}
    (hπ : π ∈ A.P ^ Q)
    (hH : IsExternalForcingFilter (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) H) :
    A.projectionQuotientFilter (A.projectionCombinedFilter Q H) = H := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.2
  · intro hx
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp (hH.1 x hx)
    exact ⟨q, ⟨hq, hx⟩, rfl⟩

noncomputable def projectionCombinedContext (A : ForcingContext V) {Q S π t : V}
    {H : Set A.Model} (hπ : IsForcingProjection A.P A.R Q S π)
    (hS : IsForcingPreorder Q S) (ht : IsForcingTop Q S t)
    (hH : IsExternalForcingGeneric (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) H) : ForcingContext V where
  P := Q
  R := S
  one := t
  G := A.projectionCombinedFilter Q H
  order := hS
  top := ht
  generic := A.projectionCombined_generic hπ hS hH

end ForcingContext
end ZFVP
