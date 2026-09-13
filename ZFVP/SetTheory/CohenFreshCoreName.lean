import ZFVP.SetTheory.CohenFixedOrbitName
import ZFVP.SetTheory.CohenOrbitMemberTransfer

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- All fresh supported members, with coefficients localized below `p` before projection. -/
noncomputable def cohenFreshCoreName (U τ E F p : V) : V :=
  {z ∈ U ×ˢ cohenConditions (ω : V) ;
    IsForcingName (cohenConditions (ω : V)) (kpair.π₁ z) ∧
    ∃ D, IsCohenNameSupport (kpair.π₁ z) D ∧
      (∀ i ∈ D, i ∈ E ∪ F → i ∈ E ∩ F) ∧
      ∃ r, ⟨r, p⟩ₖ ∈ cohenOrder (ω : V) ∧
        r ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) (kpair.π₁ z) τ ∧
        kpair.π₂ z = cohenConditionRestrict r (D ∪ (E ∩ F))}

theorem pair_mem_cohenFreshCoreName (U τ E F p μ q : V) :
    ⟨μ, q⟩ₖ ∈ cohenFreshCoreName U τ E F p ↔
      μ ∈ U ∧ q ∈ cohenConditions (ω : V) ∧
      IsForcingName (cohenConditions (ω : V)) μ ∧
      ∃ D, IsCohenNameSupport μ D ∧
        (∀ i ∈ D, i ∈ E ∪ F → i ∈ E ∩ F) ∧
        ∃ r, ⟨r, p⟩ₖ ∈ cohenOrder (ω : V) ∧
          r ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ ∧
          q = cohenConditionRestrict r (D ∪ (E ∩ F)) := by
  simp only [cohenFreshCoreName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem cohenFreshCoreName_isName (U τ E F p : V) :
    IsForcingName (cohenConditions (ω : V)) (cohenFreshCoreName U τ E F p) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨μ, hμ, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨μ, q, hq, rfl, ((pair_mem_cohenFreshCoreName _ _ _ _ _ _ _).mp hz).2.2.1⟩

theorem cohenFreshCoreName_orbit_member {U τ σ E F p μ s q : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (hm : ⟨μ, s⟩ₖ ∈ cohenFixedOrbitName (E ∩ F) (cohenFreshCoreName U τ E F p))
    (hq : q ∈ cohenConditions (ω : V))
    (hqp : ⟨q, p⟩ₖ ∈ cohenOrder (ω : V))
    (hqs : ⟨q, s⟩ₖ ∈ cohenOrder (ω : V)) :
    q ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ := by
  obtain ⟨a, ha, hafix, ν, t, ht, he⟩ :=
    (mem_cohenFixedOrbitName (cohenFreshCoreName_isName U τ E F p) _).mp hm
  obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
  obtain ⟨_, htP, hν, D, hD, hfresh, r, hrp, hrν, rfl⟩ :=
    (pair_mem_cohenFreshCoreName _ _ _ _ _ _ _).mp ht
  rw [cohenPermutation_value htP] at hqs
  exact cohen_orbitMember_transfer hτ hσ hν hE hF hD hp hsupp hfresh hrp hrν ha hafix hq hqp hqs

end ZFVP
