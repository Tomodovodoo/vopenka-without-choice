import ZFVP.ModelTheory.CohenModel
import ZFVP.SetTheory.CohenStableRepresentativeSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Every evaluated Cohen-model name has a least finite representative support. The minimum
is obtained from an internally coded dense set, so no external finiteness assumption is used. -/
theorem evaluatedName_exists_least_support
    (τ : (cohenContext (ω : V) G hG).Name) :
    ∃ E, ∃ ν : (cohenContext (ω : V) G hG).Name,
      (cohenContext (ω : V) G hG).ofName ν = (cohenContext (ω : V) G hG).ofName τ ∧
      IsCohenNameSupport ν.val E ∧
      ∀ (σ : (cohenContext (ω : V) G hG).Name) F,
        (cohenContext (ω : V) G hG).ofName σ = (cohenContext (ω : V) G hG).ofName τ →
        IsCohenNameSupport σ.val F → E ⊆ F := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨q, hqG, hqst⟩ := hG.2 _ (cohenSupportStabilizers_dense τ.property)
  have hq := hG.1.1 q hqG
  have hstable := (mem_sep_iff.mp hqst).2
  let E := cohenRepresentativeLeastSupport τ.val q
  obtain ⟨ν, hν, heν, hE⟩ := cohenRepresentativeLeastSupport_isSupport τ.property hq
  refine ⟨E, ⟨ν, hν⟩, ?_, hE, ?_⟩
  · exact (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ ⟨ν, hν⟩ τ).mpr
      ⟨q, hqG, heν⟩
  · intro σ F he hF
    obtain ⟨r, hrG, hrEq⟩ :=
      (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ σ τ).mp he
    obtain ⟨t, htG, htq, htr⟩ := hG.1.2.2.2 q hqG r hrG
    have ht := hG.1.1 t htG
    have hFt : IsCohenRepresentativeSupport τ.val t F :=
      ⟨σ.val, σ.property, atomicEquality_mono S.order hrEq ht htr, hF⟩
    have hh := cohenRepresentativeLeastSupport_subset hFt
    rwa [hstable t ht htq] at hh

end CohenModel

end ZFVP
