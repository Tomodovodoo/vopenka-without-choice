import ZFVP.ModelTheory.ProjectionBoundedTruth
import ZFVP.ModelTheory.ForcingRegularGenericEquality
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingSplitProjection.subset_of_section_identity {P R Q S π E : V}
    (h : IsForcingSplitProjection P R Q S π E) (hE : ∀ p ∈ P, E ‘ p = p) : P ⊆ Q :=
  fun p hp ↦ hE p hp ▸ function_value_mem h.maps hp

theorem IsForcingSplitProjection.generic_trace_of_section_identity {P R Q S π E : V}
    (h : IsForcingSplitProjection P R Q S π E) (hR : IsForcingPreorder P R)
    (hE : ∀ p ∈ P, E ‘ p = p) {G : Set V} (hG : IsExternalForcingFilter Q S G)
    (p : V) : p ∈ forcingProjectionGeneric P R π G ↔ p ∈ G ∧ p ∈ P := by
  constructor
  · intro hp
    have hmem := (h.generic_iff_section hR hG hp.1).mp hp
    exact ⟨hE p hp.1 ▸ hmem, hp.1⟩
  · rintro ⟨hpG, hp⟩
    apply (h.generic_iff_section hR hG hp).mpr
    rwa [hE p hp]

/-- Bounded truth is unchanged by passing to a larger complete prefix, on
arbitrary nonempty subname-closed name pools containing the assignment. -/
theorem boundedForcing_genericMeets_projection {P R one Q S top π E D0 D1 n φ b : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hu : IsForcingTop Q S top)
    (hπ : IsForcingSplitProjection P R Q S π E) (hE : ∀ p ∈ P, E ‘ p = p)
    (hD0 : ∀ τ ∈ D0, IsForcingName P τ) (hD1 : ∀ τ ∈ D1, IsForcingName Q τ)
    (hne0 : IsNonempty D0) (hne1 : IsNonempty D1)
    (hc0 : ∀ τ ∈ D0, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D0)
    (hc1 : ∀ τ ∈ D1, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D1)
    (hφ : IsBoundedFormulaCode n φ) (hb0 : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n)
    {G : Set V} (hG : IsExternalForcingGeneric Q S G) :
    GenericMeets (forcingProjectionGeneric P R π G) (internalForcingSet P R D0 n φ b) ↔
      GenericMeets G (internalForcingSet Q S D1 n φ b) := by
  let A : ForcingContext V :=
    ⟨P, R, one, forcingProjectionGeneric P R π G, hR, ht, hπ.projection.generic hR hG⟩
  let B : ForcingContext V := ⟨Q, S, top, G, hS, hu, hG⟩
  exact A.genericInclusion_boundedForcing_meets B (hπ.subset_of_section_identity hE)
    (hπ.generic_trace_of_section_identity hR hE hG.1)
    hD0 hD1 hne0 hne1 hc0 hc1 hφ hb0 hb1

theorem boundedForcing_prefix_iff_countable [Countable V]
    {P R one Q S top π E D0 D1 n φ b p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hu : IsForcingTop Q S top)
    (hπ : IsForcingSplitProjection P R Q S π E) (hE : ∀ p ∈ P, E ‘ p = p)
    (hD0 : ∀ τ ∈ D0, IsForcingName P τ) (hD1 : ∀ τ ∈ D1, IsForcingName Q τ)
    (hne0 : IsNonempty D0) (hne1 : IsNonempty D1)
    (hc0 : ∀ τ ∈ D0, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D0)
    (hc1 : ∀ τ ∈ D1, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D1)
    (hφ : IsBoundedFormulaCode n φ) (hb0 : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n)
    (hp : p ∈ P) :
    p ∈ internalForcingSet P R D0 n φ b ↔ p ∈ internalForcingSet Q S D1 n φ b := by
  have hP := hπ.subset_of_section_identity hE
  have hreg0 := internalForcingSet_regular hR (boundedFormulaFamily_subset _ hφ) hb0
  have hreg1 := internalForcingSet_regular hS (boundedFormulaFamily_subset _ hφ) hb1
  have hagree (G : Set V) (hG : IsExternalForcingGeneric Q S G) :=
    boundedForcing_genericMeets_projection hR ht hS hu hπ hE
      hD0 hD1 hne0 hne1 hc0 hc1 hφ hb0 hb1 hG
  constructor
  · intro hf
    apply hreg1.2.2 p (hP p hp)
    intro q hq hqp
    obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hS hq
    have hpG := hG.1.2.2.1 q hqG p (hP p hp) hqp
    have hpA := (hπ.generic_trace_of_section_identity hR hE hG.1 p).mpr ⟨hpG, hp⟩
    obtain ⟨r, hrG, hr⟩ := (hagree G hG).mp ⟨p, hpA, hf⟩
    obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
    exact ⟨s, hreg1.2.1 r hr s (hG.1.1 s hsG) hsr, hsq⟩
  · intro hf
    apply hreg0.2.2 p hp
    intro q hq hqp
    obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hS (hP q hq)
    have hqE : ⟨q, p⟩ₖ ∈ S := by
      simpa only [hE q hq, hE p hp] using hπ.monotone hq hp hqp
    have hpG := hG.1.2.2.1 q hqG p (hP p hp) hqE
    obtain ⟨r, hrG, hr⟩ := (hagree G hG).mpr ⟨p, hpG, hf⟩
    have hA := hπ.projection.generic hR hG
    have hqA := (hπ.generic_trace_of_section_identity hR hE hG.1 q).mpr ⟨hqG, hq⟩
    obtain ⟨s, hsG, hsr, hsq⟩ := hA.1.2.2.2 r hrG q hqA
    exact ⟨s, hreg0.2.1 r hr s (hA.1.1 s hsG) hsr, hsq⟩

end ZFVP
