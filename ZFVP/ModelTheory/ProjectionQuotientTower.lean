import ZFVP.ModelTheory.ProjectionFactorization
import ZFVP.ModelTheory.QuotientSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_mem_projectionQuotientFilter_iff (A : ForcingContext V) (H : Set V) (q : V) :
    A.check q ∈ A.projectionQuotientFilter H ↔ q ∈ H := by
  constructor
  · rintro ⟨r, hr, he⟩
    exact (A.check_eq_iff q r).mp he ▸ hr
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- Quotienting a second time tests the later projection against the later
generic. The first generic membership follows from the commuting projections. -/
theorem double_projectionQuotient_check_mem_iff (A : ForcingContext V)
    (B : ForcingContext A.Model) {Q T U π τ ρ q : V} {H : Set V}
    (hπ : π ∈ A.P ^ Q) (hτ : IsForcingProjection A.P A.R T U τ)
    (hρ : ρ ∈ T ^ Q) (he : ∀ r ∈ Q, τ ‘ (ρ ‘ r) = π ‘ r)
    (hH : IsExternalForcingFilter T U H)
    (hA : forcingProjectionGeneric A.P A.R τ H = A.G)
    (hBP : B.P = A.projectionQuotient T τ)
    (hBG : B.G = A.projectionQuotientFilter H) :
    B.check (A.check q) ∈ B.projectionQuotient (A.projectionQuotient Q π)
      (A.projectionQuotientMap Q π ρ) ↔ q ∈ Q ∧ ρ ‘ q ∈ H := by
  have hm := A.projectionQuotientMap_maps hπ hτ.maps hρ he
  have hmB : A.projectionQuotientMap Q π ρ ∈ B.P ^ A.projectionQuotient Q π := hBP.symm ▸ hm
  rw [B.check_mem_projectionQuotient_iff hmB]
  constructor
  · rintro ⟨hq, hg⟩
    have hqQ := ((A.check_mem_projectionQuotient_iff hπ).mp hq).1
    rw [A.projectionQuotientMap_value hρ hqQ hq, hBG,
      A.check_mem_projectionQuotientFilter_iff] at hg
    exact ⟨hqQ, hg⟩
  · rintro ⟨hq, hg⟩
    have hbase : π ‘ q ∈ A.G := by
      rw [← he q hq, ← hA]
      exact hτ.image_mem A.order hH hg
    have hq' := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq, hbase⟩
    refine ⟨hq', ?_⟩
    rw [A.projectionQuotientMap_value hρ hq hq', hBG,
      A.check_mem_projectionQuotientFilter_iff]
    exact hg

theorem double_projectionQuotient_mem_iff (A : ForcingContext V)
    (B : ForcingContext A.Model) {Q T U π τ ρ : V} {H : Set V}
    (hπ : π ∈ A.P ^ Q) (hτ : IsForcingProjection A.P A.R T U τ)
    (hρ : ρ ∈ T ^ Q) (he : ∀ r ∈ Q, τ ‘ (ρ ‘ r) = π ‘ r)
    (hH : IsExternalForcingFilter T U H)
    (hA : forcingProjectionGeneric A.P A.R τ H = A.G)
    (hBP : B.P = A.projectionQuotient T τ)
    (hBG : B.G = A.projectionQuotientFilter H) (x : B.Model) :
    x ∈ B.projectionQuotient (A.projectionQuotient Q π)
      (A.projectionQuotientMap Q π ρ) ↔
      ∃ q ∈ Q, ρ ‘ q ∈ H ∧ x = B.check (A.check q) := by
  have hm := A.projectionQuotientMap_maps hπ hτ.maps hρ he
  have hmB : A.projectionQuotientMap Q π ρ ∈ B.P ^ A.projectionQuotient Q π := hBP.symm ▸ hm
  constructor
  · intro hx
    obtain ⟨y, hy, _, rfl⟩ := (B.mem_projectionQuotient_iff hmB x).mp hx
    obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
    exact ⟨q, hq, ((A.double_projectionQuotient_check_mem_iff B hπ hτ hρ he
      hH hA hBP hBG).mp hx).2, rfl⟩
  · rintro ⟨q, hq, hg, rfl⟩
    exact (A.double_projectionQuotient_check_mem_iff B hπ hτ hρ he
      hH hA hBP hBG).mpr ⟨hq, hg⟩

theorem double_projectionQuotientOrder_pair_iff (A : ForcingContext V)
    (B : ForcingContext A.Model) {Q S T U π τ ρ q r : V} {H : Set V}
    (hπ : π ∈ A.P ^ Q) (hτ : IsForcingProjection A.P A.R T U τ)
    (hρ : ρ ∈ T ^ Q) (he : ∀ s ∈ Q, τ ‘ (ρ ‘ s) = π ‘ s)
    (hH : IsExternalForcingFilter T U H)
    (hA : forcingProjectionGeneric A.P A.R τ H = A.G)
    (hBP : B.P = A.projectionQuotient T τ)
    (hBG : B.G = A.projectionQuotientFilter H) :
    ⟨B.check (A.check q), B.check (A.check r)⟩ₖ ∈
      B.projectionQuotientOrder (A.projectionQuotient Q π)
        (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ) ↔
      ⟨q, r⟩ₖ ∈ S ∧ (q ∈ Q ∧ ρ ‘ q ∈ H) ∧ (r ∈ Q ∧ ρ ‘ r ∈ H) := by
  rw [B.projectionQuotientOrder_pair_iff, ← B.check_kpair, B.check_mem_iff,
    A.projectionQuotientOrder_pair_iff, ← A.check_kpair, A.check_mem_iff]
  rw [A.double_projectionQuotient_check_mem_iff B hπ hτ hρ he hH hA hBP hBG,
    A.double_projectionQuotient_check_mem_iff B hπ hτ hρ he hH hA hBP hBG]
  constructor
  · rintro ⟨⟨hqr, _, _⟩, hq, hr⟩
    exact ⟨hqr, hq, hr⟩
  · rintro ⟨hqr, hq, hr⟩
    have hb : ∀ s ∈ Q, ρ ‘ s ∈ H → A.check s ∈ A.projectionQuotient Q π := by
      intro s hs hg
      apply (A.check_mem_projectionQuotient_iff hπ).mpr
      refine ⟨hs, ?_⟩
      rw [← he s hs, ← hA]
      exact hτ.image_mem A.order hH hg
    exact ⟨⟨hqr, hb q hq.1 hq.2, hb r hr.1 hr.2⟩, hq, hr⟩

theorem projectionFactorizationEquiv_quotient (A C : ForcingContext V) {Q π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ C.P ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) :
    A.projectionFactorizationEquiv C hτ hA
      ((A.projectionQuotientContext C hτ hA).projectionQuotient
        (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ)) =
      C.projectionQuotient Q ρ := by
  let B := A.projectionQuotientContext C hτ hA
  let e := A.projectionFactorizationEquiv C hτ hA
  apply mem_ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [A.projectionFactorizationEquiv_mem_iff,
    A.double_projectionQuotient_mem_iff B hπ hτ.projection hρ he C.generic.1 hA rfl rfl,
    C.mem_projectionQuotient_iff hρ]
  constructor
  · rintro ⟨q, hq, hg, rfl⟩
    exact ⟨q, hq, hg, A.projectionFactorizationEquiv_ground C hτ hA q⟩
  · rintro ⟨q, hq, hg, hqx⟩
    refine ⟨q, hq, hg, e.injective ?_⟩
    exact hqx.trans (A.projectionFactorizationEquiv_ground C hτ hA q).symm

theorem projectionFactorizationEquiv_quotientOrder (A C : ForcingContext V) {Q S π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ C.P ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) :
    A.projectionFactorizationEquiv C hτ hA
      ((A.projectionQuotientContext C hτ hA).projectionQuotientOrder
        (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
        (A.projectionQuotientMap Q π ρ)) = C.projectionQuotientOrder Q S ρ := by
  let B := A.projectionQuotientContext C hτ hA
  let e := A.projectionFactorizationEquiv C hτ hA
  have hpairs (q r : V) : e ⟨B.check (A.check q), B.check (A.check r)⟩ₖ =
      ⟨C.check q, C.check r⟩ₖ := by
    rw [← B.check_kpair, ← A.check_kpair]
    exact (A.projectionFactorizationEquiv_ground C hτ hA _).trans (C.check_kpair q r)
  apply mem_ext
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [A.projectionFactorizationEquiv_mem_iff]
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hx).2
    obtain ⟨q, hq, hgq, rfl⟩ := (A.double_projectionQuotient_mem_iff B hπ
      hτ.projection hρ he C.generic.1 hA rfl rfl a).mp ha
    obtain ⟨r, hr, hgr, rfl⟩ := (A.double_projectionQuotient_mem_iff B hπ
      hτ.projection hρ he C.generic.1 hA rfl rfl b).mp hb
    have hqr := ((A.double_projectionQuotientOrder_pair_iff B hπ hτ.projection
      hρ he C.generic.1 hA rfl rfl).mp hx).1
    rw [hpairs, C.projectionQuotientOrder_pair_iff, ← C.check_kpair, C.check_mem_iff]
    exact ⟨hqr, (C.check_mem_projectionQuotient_iff hρ).mpr ⟨hq, hgq⟩,
      (C.check_mem_projectionQuotient_iff hρ).mpr ⟨hr, hgr⟩⟩
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp (mem_sep_iff.mp hx).2
    obtain ⟨q, hq, hgq, rfl⟩ := (C.mem_projectionQuotient_iff hρ a).mp ha
    obtain ⟨r, hr, hgr, rfl⟩ := (C.mem_projectionQuotient_iff hρ b).mp hb
    have hxe : x = ⟨B.check (A.check q), B.check (A.check r)⟩ₖ :=
      e.injective (hab.trans (hpairs q r).symm)
    rw [hxe, A.double_projectionQuotientOrder_pair_iff B hπ hτ.projection
      hρ he C.generic.1 hA rfl rfl]
    have hqr := ((C.projectionQuotientOrder_pair_iff Q S ρ _ _).mp (hab ▸ hx)).1
    rw [← C.check_kpair, C.check_mem_iff] at hqr
    exact ⟨hqr, ⟨hq, hgq⟩, ⟨hr, hgr⟩⟩

end ForcingContext
end ZFVP
