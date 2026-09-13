import ZFVP.SetTheory.CohenFreshCoreName
import ZFVP.SetTheory.CohenFreshReverseTransfer
import ZFVP.SetTheory.CohenSupportTransport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cohenFreshCoreName_orbit_contains {U τ σ E F p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (hU : ∀ μ s, ⟨μ, s⟩ₖ ∈ τ → ∀ b, IsInternalPermutation (ω : V) b →
      nameAction (cohenPermutation (ω : V) b) μ ∈ U)
    {μ s q : V} (hm : ⟨μ, s⟩ₖ ∈ τ) (hq : q ∈ cohenConditions (ω : V))
    (hqp : ⟨q, p⟩ₖ ∈ cohenOrder (ω : V))
    (hqs : ⟨q, s⟩ₖ ∈ cohenOrder (ω : V)) :
    q ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ
      (cohenFixedOrbitName (E ∩ F) (cohenFreshCoreName U τ E F p)) := by
  have hR := (cohen_poset (ω : V)).1
  have hpP := atomicEquality_subset _ _ _ _ p hp
  have hμhs := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 μ s hm
  obtain ⟨D, hDω, hDf, hDs⟩ := cohenName_finiteSupport hμhs
  have hD : IsCohenNameSupport μ D := ⟨hDω, hDf, hDs⟩
  have hqμ := atomicMembership_mono hR
    (atomicMembership_of_pair hR (forcingName_condition hτ.1 hm) hm) hq hqs
  apply atomicMembership_dense hR hq
  intro t ht htq
  have htp := hR.2.2 t ht q hq p hpP htq hqp
  have htμ := atomicMembership_mono hR hqμ ht htq
  obtain ⟨b, v, hb, hbfix, hfresh, hv, hvp, hvbt, hvμ⟩ :=
    cohen_fresh_reverse_transfer hτ.1 hσ hμhs.1 hE hF hD hp hsupp htp htμ
  let D' := repl (fun i ↦ b ‘ i) (by definability) D
  let q₀ := cohenConditionRestrict v (D' ∪ (E ∩ F))
  have hq₀ := cohenConditionRestrict_condition hv (D' ∪ (E ∩ F))
  have hcore : ⟨nameAction (cohenPermutation (ω : V) b) μ, q₀⟩ₖ ∈
      cohenFreshCoreName U τ E F p := by
    apply (pair_mem_cohenFreshCoreName _ _ _ _ _ _ _).mpr
    exact ⟨hU μ s hm b hb, hq₀,
      nameAction_isName (cohenPermutation_automorphism hb).1 hμhs.1,
      D', hD.image hμhs.1 hb, hfresh, v, hvp, hvμ, rfl⟩
  have ha := cohenPermutation_automorphism hb
  have hai := forcingAutomorphism_inverse ha
  have hbinvfix : ∀ i ∈ E ∩ F, (converseGraph b) ‘ i = i := by
    intro i hi
    have hh := hb.inv_value (hE.1 i (mem_inter_iff.mp hi).1)
    rwa [hbfix i hi] at hh
  have hpair : ⟨μ, (converseGraph (cohenPermutation (ω : V) b)) ‘ q₀⟩ₖ ∈
      cohenFixedOrbitName (E ∩ F) (cohenFreshCoreName U τ E F p) := by
    apply (mem_cohenFixedOrbitName (cohenFreshCoreName_isName U τ E F p) _).mpr
    refine ⟨converseGraph b, hb.inv, hbinvfix, _, q₀, hcore, ?_⟩
    rw [cohenPermutation_inverse hb, nameAction_inverse_cancel ha hμhs.1]
  let u := (converseGraph (cohenPermutation (ω : V) b)) ‘ v
  have hu : u ∈ cohenConditions (ω : V) := function_value_mem hai.1 hv
  have hut : ⟨u, t⟩ₖ ∈ cohenOrder (ω : V) := by
    rw [← cohenPermutation_value ht] at hvbt
    have hh := (hai.2.2.2 v hv _ (function_value_mem ha.1 ht)).mp hvbt
    rwa [converseGraph_value_value ha.1 ha.2.1 ht] at hh
  have huq₀ : ⟨u, (converseGraph (cohenPermutation (ω : V) b)) ‘ q₀⟩ₖ ∈
      cohenOrder (ω : V) := by
    apply (hai.2.2.2 v hv q₀ hq₀).mp
    exact (pair_mem_cohenOrder _ _ _).mpr ⟨hv, hq₀, cohenConditionRestrict_subset _ _⟩
  exact ⟨u, atomicMembership_mono hR
    (atomicMembership_of_pair hR (function_value_mem hai.1 hq₀) hpair) hu huq₀, hut⟩

/-- Equality below a condition whose coordinates lie in the two supports has a common
hereditarily symmetric representative supported by their intersection. -/
theorem cohen_representative_intersection_supported_condition {τ σ E F p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hσ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F) :
    ∃ ν, IsHereditarilySymmetricName (cohenConditions (ω : V))
        (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧
      p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν τ ∧
      IsCohenNameSupport ν (E ∩ F) := by
  let U := nameOrbit (cohenGroup (ω : V)) (domain τ)
  let N := cohenFreshCoreName U τ E F p
  let ν := cohenFixedOrbitName (E ∩ F) N
  have hΓ := cohenGroup_group (ω : V)
  have hH := forcingGroup_subgroup_self hΓ
  have hdom : ∀ μ ∈ domain τ, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) μ := by
    intro μ hμ
    obtain ⟨s, hs⟩ := mem_domain_iff.mp hμ
    exact (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 μ s hs
  have hUhs : ∀ μ ∈ U, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) μ :=
    fun _ hμ ↦ hereditarilySymmetric_mem_nameOrbit hΓ (cohenFilter_normal (ω : V)) hH hdom hμ
  have hCω : E ∩ F ⊆ (ω : V) := fun i hi ↦ hE.1 i (mem_inter_iff.mp hi).1
  have hCf : IsInternallyFinite (E ∩ F) :=
    internallyFinite_subset hE.2.1 (fun _ hi ↦ (mem_inter_iff.mp hi).1)
  have hN : IsForcingName (cohenConditions (ω : V)) N := cohenFreshCoreName_isName U τ E F p
  have hν : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν := by
    apply cohenFixedOrbitName_hereditarilySymmetric hCω hCf hN
    intro μ q hm
    exact hUhs μ ((pair_mem_cohenFreshCoreName _ _ _ _ _ _ _).mp hm).1
  refine ⟨ν, hν, ?_, hCω, hCf, fun π hπ hfix ↦ cohenFixedOrbitName_fixed hCω hN hπ hfix⟩
  apply (atomicEquality_iff_membership _ _ _ _ _ (cohen_poset (ω : V)).1).mpr
  refine ⟨atomicEquality_subset _ _ _ _ p hp, ?_, ?_⟩
  · intro μ s hs q hq hqp hqs
    exact cohenFreshCoreName_orbit_member hτ.1 hσ.1 hE hF hp hsupp hs hq hqp hqs
  · intro μ s hs q hq hqp hqs
    apply cohenFreshCoreName_orbit_contains hτ hσ.1 hE hF hp hsupp ?_ hs hq hqp hqs
    intro κ t hκ b hb
    have hκdom := mem_domain_of_kpair_mem hκ
    have hκU := subset_nameOrbit hH (fun μ hμ ↦ (hdom μ hμ).1) κ hκdom
    exact (nameOrbit_action_iff hΓ hH (fun μ hμ ↦ (hdom μ hμ).1)
      ((mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩) (forcingName_subname hτ.1 hκ)).mpr hκU

/-- The exact representative-intersection theorem: the equality condition contributes no
extra coordinates to the resulting support. -/
theorem cohen_representative_intersection_below {τ σ E F p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hσ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ) :
    ∃ ν, IsHereditarilySymmetricName (cohenConditions (ω : V))
        (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧
      p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν τ ∧
      IsCohenNameSupport ν (E ∩ F) := by
  have hBω : E ∪ F ⊆ (ω : V) :=
    fun i hi ↦ (mem_union_iff.mp hi).elim (hE.1 i) (hF.1 i)
  have hBf := internallyFinite_union hE.2.1 hF.2.1
  have hE' := hE.enlarge hBω hBf (fun i hi ↦ mem_union_iff.mpr (Or.inl hi))
  have hF' := hF.enlarge hBω hBf (fun i hi ↦ mem_union_iff.mpr (Or.inr hi))
  have he := cohen_atomicEquality_restrict hτ.1 hσ.1 hE' hF' hp
  obtain ⟨ν, hν, heν, hsν⟩ :=
    cohen_representative_intersection_supported_condition hτ hσ hE hF he (by
      intro i hi
      rw [cohenConditionRestrict_support] at hi
      exact (mem_inter_iff.mp hi).2)
  refine ⟨ν, hν, atomicEquality_mono (cohen_poset (ω : V)).1 heν
    (atomicEquality_subset _ _ _ _ p hp) ?_, hsν⟩
  exact cohenConditionRestrict_weaker (atomicEquality_subset _ _ _ _ p hp) _

end ZFVP

