import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Conditions whose projection belongs to the intermediate generic filter. -/
noncomputable def projectionQuotient (A : ForcingContext V) (Q π : V) : A.Model :=
  {q ∈ A.check Q ; (A.check π) ‘ q ∈ A.genericSet}

noncomputable def projectionQuotientOrder (A : ForcingContext V) (Q S π : V) : A.Model :=
  {z ∈ A.check S ; z ∈ A.projectionQuotient Q π ×ˢ A.projectionQuotient Q π}

theorem check_mem_projectionQuotient_iff (A : ForcingContext V) {Q π q : V}
    (hπ : π ∈ A.P ^ Q) :
    A.check q ∈ A.projectionQuotient Q π ↔ q ∈ Q ∧ π ‘ q ∈ A.G := by
  let := IsFunction.of_mem hπ
  constructor
  · intro h
    obtain ⟨hq, hg⟩ := mem_sep_iff.mp h
    have hqQ := (A.check_mem_iff q Q).mp hq
    rw [A.check_value ((domain_eq_of_mem_function hπ).symm ▸ hqQ),
      A.check_mem_genericSet_iff] at hg
    exact ⟨hqQ, hg⟩
  · rintro ⟨hq, hg⟩
    apply mem_sep_iff.mpr
    refine ⟨(A.check_mem_iff q Q).mpr hq, ?_⟩
    rw [A.check_value ((domain_eq_of_mem_function hπ).symm ▸ hq),
      A.check_mem_genericSet_iff]
    exact hg

theorem mem_projectionQuotient_iff (A : ForcingContext V) {Q π : V}
    (hπ : π ∈ A.P ^ Q) (x : A.Model) :
    x ∈ A.projectionQuotient Q π ↔ ∃ q ∈ Q, π ‘ q ∈ A.G ∧ x = A.check q := by
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff Q x).mp (mem_sep_iff.mp hx).1
    exact ⟨q, hq, ((A.check_mem_projectionQuotient_iff hπ).mp hx).2, rfl⟩
  · rintro ⟨q, hq, hg, rfl⟩
    exact (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq, hg⟩

theorem projectionQuotientOrder_pair_iff (A : ForcingContext V) (Q S π : V)
    (x y : A.Model) :
    ⟨x, y⟩ₖ ∈ A.projectionQuotientOrder Q S π ↔
      ⟨x, y⟩ₖ ∈ A.check S ∧ x ∈ A.projectionQuotient Q π ∧
        y ∈ A.projectionQuotient Q π := by
  simp only [projectionQuotientOrder, mem_sep_iff, kpair_mem_iff]

theorem projectionQuotient_preorder (A : ForcingContext V) {Q S π : V}
    (hπ : π ∈ A.P ^ Q) (hS : IsForcingPreorder Q S) :
    IsForcingPreorder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    exact ⟨A.check_kpair q q ▸ (A.check_mem_iff _ _).mpr (hS.2.1 q hq), hx, hx⟩
  · intro x hx y hy z hz hxy hyz
    obtain ⟨p, hp, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
    obtain ⟨r, hr, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ z).mp hz
    have hpq := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxy).1
    have hqr := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hyz).1
    rw [← A.check_kpair, A.check_mem_iff] at hpq hqr
    apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    exact ⟨A.check_kpair p r ▸ (A.check_mem_iff _ _).mpr
      (hS.2.2 p hp q hq r hr hpq hqr), hx, hz⟩

theorem projectionQuotient_top (A : ForcingContext V) {Q S π t : V}
    (hπ : π ∈ A.P ^ Q) (ht : IsForcingTop Q S t) (he : π ‘ t = A.one) :
    IsForcingTop (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) (A.check t) := by
  have hone : A.one ∈ A.G := by
    obtain ⟨p, hp⟩ := A.generic.1.2.1
    exact A.generic.1.2.2.1 p hp A.one A.top.1 (A.top.2 p (A.generic.1.1 p hp))
  have htQ := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨ht.1, he.symm ▸ hone⟩
  refine ⟨htQ, ?_⟩
  intro x hx
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
  exact ⟨A.check_kpair q t ▸ (A.check_mem_iff _ _).mpr (ht.2 q hq), hx, htQ⟩

/-- A ground-model dense set remains dense after restriction to the quotient. -/
theorem projectionQuotient_ground_dense (A : ForcingContext V) {Q S π D : V}
    (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (hD : ForcingDense Q S D) :
    ForcingDense (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      {x ∈ A.projectionQuotient Q π ; x ∈ A.check D} := by
  refine ⟨fun x hx ↦ (mem_sep_iff.mp hx).1, ?_⟩
  intro x hx
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
  let E : V := {p ∈ A.P ; ∃ d ∈ D, ⟨d, q⟩ₖ ∈ S ∧ π ‘ d = p}
  have hE : ForcingDenseBelow A.P A.R E (π ‘ q) := by
    refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
    intro p hp hpq
    obtain ⟨r, hr, hrq, hrp⟩ := hπ.lift q hq p hp hpq
    obtain ⟨d, hd, hdr⟩ := hD.2 r hr
    have hdQ := hD.1 d hd
    refine ⟨π ‘ d, mem_sep_iff.mpr ⟨function_value_mem hπ.maps hdQ,
      d, hd, hS.2.2 d hdQ r hr q hq hdr hrq, rfl⟩, ?_⟩
    exact hrp ▸ hπ.monotone d hdQ r hr hdr
  obtain ⟨p, hpG, hpE⟩ := externalForcingGeneric_meets_denseBelow A.order A.generic hqG hE
  obtain ⟨d, hd, hdq, hdp⟩ := (mem_sep_iff.mp hpE).2
  have hdQ := (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hD.1 d hd, hdp.symm ▸ hpG⟩
  refine ⟨A.check d, mem_sep_iff.mpr ⟨hdQ, (A.check_mem_iff d D).mpr hd⟩, ?_⟩
  exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    ⟨A.check_kpair d q ▸ (A.check_mem_iff _ _).mpr hdq, hdQ, hx⟩

def projectionQuotientFilter (A : ForcingContext V) (G : Set V) : Set A.Model :=
  {x | ∃ q ∈ G, x = A.check q}

theorem projectionQuotient_filter (A : ForcingContext V) {Q S π : V} {G : Set V}
    (hπ : IsForcingProjection A.P A.R Q S π) (hG : IsExternalForcingFilter Q S G)
    (he : forcingProjectionGeneric A.P A.R π G = A.G) :
    IsExternalForcingFilter (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientFilter G) := by
  have hmem : ∀ q ∈ G, A.check q ∈ A.projectionQuotient Q π := by
    intro q hq
    exact (A.check_mem_projectionQuotient_iff hπ.maps).mpr
      ⟨hG.1 q hq, he ▸ hπ.image_mem A.order hG hq⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨q, hq, rfl⟩
    exact hmem q hq
  · obtain ⟨q, hq⟩ := hG.2.1
    exact ⟨A.check q, q, hq, rfl⟩
  · rintro x ⟨q, hq, rfl⟩ y hy hxy
    obtain ⟨r, hr, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps y).mp hy
    have hqr := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxy).1
    rw [← A.check_kpair, A.check_mem_iff] at hqr
    exact ⟨r, hG.2.2.1 q hq r hr hqr, rfl⟩
  · rintro x ⟨q, hq, rfl⟩ y ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hsq, hsr⟩ := hG.2.2.2 q hq r hr
    refine ⟨A.check s, ⟨s, hs, rfl⟩, ?_, ?_⟩
    · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
        ⟨A.check_kpair s q ▸ (A.check_mem_iff _ _).mpr hsq, hmem s hs, hmem q hq⟩
    · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
        ⟨A.check_kpair s r ▸ (A.check_mem_iff _ _).mpr hsr, hmem s hs, hmem r hr⟩

end ForcingContext
end ZFVP
