import ZFVP.ModelTheory.ProjectionQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def projectionQuotientMap (A : ForcingContext V) (Q π ρ : V) : A.Model :=
  definableGraph (A.projectionQuotient Q π) (fun x ↦ (A.check ρ) ‘ x) (by definability)

theorem projectionQuotientMap_value (A : ForcingContext V) {Q π ρ T q : V}
    (hρ : ρ ∈ T ^ Q) (hq : q ∈ Q) (hg : A.check q ∈ A.projectionQuotient Q π) :
    (A.projectionQuotientMap Q π ρ) ‘ (A.check q) = A.check (ρ ‘ q) := by
  let := IsFunction.of_mem hρ
  rw [projectionQuotientMap, value_definableGraph _ _ _ hg,
    A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hq)]

theorem projectionQuotientMap_maps (A : ForcingContext V) {Q T π τ ρ : V}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T) (hρ : ρ ∈ T ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) :
    A.projectionQuotientMap Q π ρ ∈ A.projectionQuotient T τ ^ A.projectionQuotient Q π := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  let := IsFunction.of_mem hρ
  rw [A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hq)]
  exact (A.check_mem_projectionQuotient_iff hτ).mpr
    ⟨function_value_mem hρ hq, (he q hq).symm ▸ hqG⟩

/-- A commuting ground projection induces an exact projection between quotients
over the same generic filter. -/
theorem projectionQuotient_projection (A : ForcingContext V) {Q S T U π τ ρ : V}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) :
    IsForcingProjection (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientMap Q π ρ) := by
  have hm := A.projectionQuotientMap_maps hπ hτ hρ.maps he
  refine ⟨hm, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    obtain ⟨r, hr, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
    have hqr := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxy).1
    rw [← A.check_kpair, A.check_mem_iff] at hqr
    have hx' := function_value_mem hm hx
    have hy' := function_value_mem hm hy
    rw [A.projectionQuotientMap_value hρ.maps hq hx] at hx' ⊢
    rw [A.projectionQuotientMap_value hρ.maps hr hy] at hy' ⊢
    exact (A.projectionQuotientOrder_pair_iff T U τ _ _).mpr
      ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr (hρ.monotone q hq r hr hqr), hx', hy'⟩
  · intro x hx y hy hyx
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    obtain ⟨p, hp, hpG, rfl⟩ := (A.mem_projectionQuotient_iff hτ y).mp hy
    rw [A.projectionQuotientMap_value hρ.maps hq hx] at hyx
    have hpq := ((A.projectionQuotientOrder_pair_iff T U τ _ _).mp hyx).1
    rw [← A.check_kpair, A.check_mem_iff] at hpq
    obtain ⟨r, hr, hrq, her⟩ := hρ.lift q hq p hp hpq
    have hrG : π ‘ r ∈ A.G := by rw [← he r hr, her]; exact hpG
    have hr' := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hr, hrG⟩
    refine ⟨A.check r, hr', ?_, ?_⟩
    · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
        ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr hrq, hr', hx⟩
    · rw [A.projectionQuotientMap_value hρ.maps hr hr', her]

/-- Split projections descend to the intermediate quotients, including their
order adjunction. -/
theorem projectionQuotient_splitProjection (A : ForcingContext V) {Q S T U π τ ρ E : V}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (h : IsForcingSplitProjection T U Q S ρ E)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) :
    IsForcingSplitProjection (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientMap Q π ρ) (A.projectionQuotientMap T τ E) := by
  have hE : ∀ p ∈ T, π ‘ (E ‘ p) = τ ‘ p := by
    intro p hp
    rw [← he _ (function_value_mem h.maps hp), h.right_inverse p hp]
  have hm := A.projectionQuotientMap_maps hτ hπ h.maps hE
  have hproj := A.projectionQuotient_projection hπ hτ h.projection he
  refine ⟨hproj, hm, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, _, rfl⟩ := (A.mem_projectionQuotient_iff hτ x).mp hx
    have hx' := function_value_mem hm hx
    rw [A.projectionQuotientMap_value h.maps hp hx] at hx' ⊢
    rw [A.projectionQuotientMap_value h.projection.maps (function_value_mem h.maps hp) hx',
      h.right_inverse p hp]
  · intro x hx y hy
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    obtain ⟨p, hp, _, rfl⟩ := (A.mem_projectionQuotient_iff hτ y).mp hy
    have hx' := function_value_mem hproj.maps hx
    have hy' := function_value_mem hm hy
    rw [A.projectionQuotientMap_value h.projection.maps hq hx] at hx' ⊢
    rw [A.projectionQuotientMap_value h.maps hp hy] at hy' ⊢
    rw [A.projectionQuotientOrder_pair_iff, A.projectionQuotientOrder_pair_iff]
    simp only [hx, hy, hx', hy', and_true, ← A.check_kpair, A.check_mem_iff]
    exact h.below q hq p hp

end ForcingContext
end ZFVP
