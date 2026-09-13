import ZFVP.ModelTheory.CohenOrbitFamily
import ZFVP.SetTheory.CohenRepresentativePool
import ZFVP.SetTheory.CohenStableRepresentativeSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- A single ground set of supported representatives contains a least-support representative
of every member of the evaluated set. -/
theorem exists_least_support_pool (X : (cohenContext (ω : V) G hG).Name) :
    ∃ D : V, ∃ _hD : IsCohenSupportPool D,
      ∀ x ∈ (cohenContext (ω : V) G hG).ofName X,
        ∃ ν : (cohenContext (ω : V) G hG).Name, ∃ E : V,
          ⟨ν.val, E⟩ₖ ∈ D ∧
          (cohenContext (ω : V) G hG).ofName ν = x ∧ IsCohenNameSupport ν.val E ∧
          ∀ (σ : (cohenContext (ω : V) G hG).Name) F,
            (cohenContext (ω : V) G hG).ofName σ = x → IsCohenNameSupport σ.val F → E ⊆ F := by
  let S := cohenContext (ω : V) G hG
  have hA : ∀ μ ∈ domain X.val, IsHereditarilySymmetricName S.P S.Γ S.F μ := by
    intro μ hμ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hμ
    exact (hereditarilySymmetric_iff _ _ _ _).mp X.property |>.2 μ p hp
  obtain ⟨D, hvalid, hcover⟩ := cohen_representative_pool hA
  have hD : IsCohenSupportPool D := by
    intro z hz
    obtain ⟨ν, E, rfl, hν, hE⟩ := hvalid z hz
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hν hE
  refine ⟨D, hD, ?_⟩
  intro x hx
  obtain ⟨τ, s, _, hτs, hxτ⟩ := (S.mem_ofName_iff X x).mp hx
  have hτA := mem_domain_of_kpair_mem hτs
  obtain ⟨q, hqG, hqst⟩ := hG.2 _ (cohenSupportStabilizers_dense τ.property)
  have hq := hG.1.1 q hqG
  have hstable := (mem_sep_iff.mp hqst).2
  let E := cohenRepresentativeLeastSupport τ.val q
  obtain ⟨ν, hνD, heν⟩ := hcover τ.val hτA q hq
  have hνs : IsHereditarilySymmetricName (cohenConditions (ω : V)) (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧ IsCohenNameSupport ν E := by
    have hh := hD ⟨ν, E⟩ₖ hνD
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hh
  refine ⟨⟨ν, hνs.1⟩, E, hνD, ?_, hνs.2, ?_⟩
  · apply Eq.trans ?_ hxτ.symm
    exact (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ ⟨ν, hνs.1⟩ τ).mpr
      ⟨q, hqG, heν⟩
  · intro σ F he hF
    obtain ⟨r, hrG, hrEq⟩ :=
      (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ σ τ).mp (he.trans hxτ)
    obtain ⟨t, htG, htq, htr⟩ := hG.1.2.2.2 q hqG r hrG
    have ht := hG.1.1 t htG
    have hFt : IsCohenRepresentativeSupport τ.val t F :=
      ⟨σ.val, σ.property, atomicEquality_mono S.order hrEq ht htr, hF⟩
    have hh := cohenRepresentativeLeastSupport_subset hFt
    rwa [hstable t ht htq] at hh

end CohenModel

end ZFVP


