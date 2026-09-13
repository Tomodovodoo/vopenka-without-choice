import ZFVP.ModelTheory.CanonicalNormalizationForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingRestrictedNameFormula : SetTheorySemisentence 5 :=
  f“N P R p t. ∀ z, z ∈ N ↔ z ∈ !prod.dfn (!domain.dfn t) P ∧
    !kpair.dfn (!kpair.π₂.dfn z) p ∈ R ∧ ∃ q ∈ P,
      !kpair.dfn (!kpair.π₁.dfn z) q ∈ t ∧ !kpair.dfn (!kpair.π₂.dfn z) q ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Restrict the root conditions of a name below p. -/
noncomputable def forcingRestrictedName (P R p τ : V) : V :=
  {z ∈ domain τ ×ˢ P ; ⟨kpair.π₂ z, p⟩ₖ ∈ R ∧
    ∃ q ∈ P, ⟨kpair.π₁ z, q⟩ₖ ∈ τ ∧ ⟨kpair.π₂ z, q⟩ₖ ∈ R}

instance forcingRestrictedNameFormula_defined :
    ℒₛₑₜ-function₄[V] forcingRestrictedName via forcingRestrictedNameFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRestrictedNameFormula, forcingRestrictedName]⟩

instance forcingRestrictedName_definable : ℒₛₑₜ-function₄[V] forcingRestrictedName :=
  forcingRestrictedNameFormula_defined.to_definable

theorem pair_mem_forcingRestrictedName (P R p τ σ r : V) :
    ⟨σ, r⟩ₖ ∈ forcingRestrictedName P R p τ ↔
      r ∈ P ∧ ⟨r, p⟩ₖ ∈ R ∧ ∃ q ∈ P, ⟨σ, q⟩ₖ ∈ τ ∧ ⟨r, q⟩ₖ ∈ R := by
  simp only [forcingRestrictedName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · exact fun h ↦ ⟨h.1.2, h.2⟩
  · rintro ⟨hr, hrp, q, hq, hσq, hrq⟩
    exact ⟨⟨mem_domain_of_kpair_mem hσq, hr⟩, hrp, q, hq, hσq, hrq⟩

theorem forcingRestrictedName_isName {P R p τ : V} (hτ : IsForcingName P τ) :
    IsForcingName P (forcingRestrictedName P R p τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hr, _, q, _, hσq, _⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hz
  exact ⟨σ, r, hr, rfl, forcingName_subname hτ hσq⟩

theorem forcingRestrictedName_mem {P R p τ δ : V} [IsOrdinal δ]
    (hτ : τ ∈ forcingNameHierarchy P δ) :
    forcingRestrictedName P R p τ ∈ forcingNameHierarchy P δ := by
  obtain ⟨β, hβ, hb⟩ := (mem_forcingNameHierarchy _ _ _).mp hτ
  apply (mem_forcingNameHierarchy _ _ _).mpr
  refine ⟨β, hβ, ?_⟩
  intro z hz
  obtain ⟨σ, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hr, _, q, _, hσq, _⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hz
  exact kpair_mem_iff.mpr ⟨(kpair_mem_iff.mp (hb _ hσq)).1, hr⟩

/-- A forced empty value becomes the literal empty name after restriction. -/
theorem forcingRestrictedName_empty_of_forced {P R p τ : V}
    (hR : IsForcingPreorder P R)
    (he : p ∈ atomicEquality P R τ ∅) : forcingRestrictedName P R p τ = ∅ := by
  apply subset_empty_iff_eq_empty.mp
  intro z hz
  obtain ⟨σ, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hr, hrp, q, hq, hσq, hrq⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hz
  have hm := atomicMembership_mono hR (atomicMembership_of_pair hR hq hσq) hr hrq
  have hbad := atomicMembership_subst_right hR (atomicEquality_mono hR he hr hrp) hm
  rw [atomicMembership_empty hR σ] at hbad
  exact False.elim (not_mem_empty hbad)

theorem forcingRestrictedName_forces {P R p : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (τ : V) :
    p ∈ atomicEquality P R (forcingRestrictedName P R p τ) τ := by
  apply (atomicEquality_iff_membership _ _ _ _ _ hR).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro σ r hσr q hq _ hqr
    obtain ⟨hr, _, s, hs, hσs, hrs⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hσr
    exact atomicMembership_mono hR (atomicMembership_of_pair hR hs hσs) hq
      (hR.2.2 q hq r hr s hs hqr hrs)
  · intro σ r hσr q hq hqp hqr
    apply atomicMembership_of_pair hR hq
    exact (pair_mem_forcingRestrictedName _ _ _ _ _ _).mpr
      ⟨hq, hqp, r, forcingOrder_right_mem hR hqr, hσr, hqr⟩

namespace ForcingContext

theorem restrictedName_value (A : ForcingContext V) {p : V} (hp : p ∈ A.G)
    (τ : ForcingName A.P) :
    A.ofName ⟨forcingRestrictedName A.P A.R p τ.val, forcingRestrictedName_isName τ.property⟩ =
      A.ofName τ := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_iff, A.mem_ofName_iff]
  constructor
  · rintro ⟨σ, r, hrG, hσr, he⟩
    obtain ⟨_, _, q, hq, hσq, hrq⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hσr
    exact ⟨σ, q, A.generic.1.2.2.1 r hrG q hq hrq, hσq, he⟩
  · rintro ⟨σ, q, hqG, hσq, he⟩
    obtain ⟨r, hrG, hrp, hrq⟩ := A.generic.1.2.2.2 p hp q hqG
    exact ⟨σ, r, hrG, (pair_mem_forcingRestrictedName _ _ _ _ _ _).mpr
      ⟨A.generic.1.1 r hrG, hrp, q, A.generic.1.1 q hqG, hσq, hrq⟩, he⟩

end ForcingContext
end ZFVP
