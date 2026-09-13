import ZFVP.ModelTheory.NormalizedTwoStepGenerics
import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameTwoStepPrefix (C : V) : V :=
  definableGraph C kpair.π₁ (by definability)

theorem nameTwoStepPrefix_value {C z : V} (hz : z ∈ C) :
    (nameTwoStepPrefix C) ‘ z = kpair.π₁ z := value_definableGraph _ _ _ hz

theorem nameTwoStepPrefix_projection {P R one δ Q S C : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hI : IsForcingIterand P R Q S ∅)
    (hC : C ⊆ boundedNameTwoStep P R δ Q)
    (hreplace : ∀ p τ, ⟨p, τ⟩ₖ ∈ C → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, τ⟩ₖ ∈ C) :
    IsForcingProjection P R C (nameTwoStepOrderOn P R S C) (nameTwoStepPrefix C) := by
  refine ⟨?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hC z hz)).1
    simpa using hp
  · intro z hz w hw he
    rw [nameTwoStepPrefix_value hz, nameTwoStepPrefix_value hw]
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (mem_sep_iff.mp he).2.1
  · intro z hz q hq hqz
    rw [nameTwoStepPrefix_value hz] at hqz
    have hb := hC z hz
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hb).1
    simp only [kpair.π₁_kpair] at hqz
    obtain ⟨_, _, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hb
    have hr := hreplace p τ hz q hq hqz
    refine ⟨⟨q, τ⟩ₖ, hr, (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr ⟨hr, hz, hqz, ?_⟩, ?_⟩
    · exact forcedPreorder_refl hR ht hq ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨τ, hτ⟩
        (hI.preorder q hq) (atomicMembership_mono hR hm hq hqz)
    · rw [nameTwoStepPrefix_value hr, kpair.π₁_kpair]

theorem boundedNameTwoStep_prefix_projection {P R one δ Q S : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingProjection P R (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q))
      (nameTwoStepPrefix (boundedNameTwoStep P R δ Q)) := by
  apply nameTwoStepPrefix_projection hR ht hI (fun _ hz ↦ hz)
  intro p τ hp q hq hqp
  obtain ⟨_, hτδ, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hp
  exact (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr
    ⟨hq, hτδ, hτ, atomicMembership_mono hR hm hq hqp⟩

theorem normalizedNameTwoStep_prefix_projection {P R one δ Q S : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingProjection P R (normalizedNameTwoStep P R one δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q))
      (nameTwoStepPrefix (normalizedNameTwoStep P R one δ Q)) := by
  apply nameTwoStepPrefix_projection hR ht hI (normalizedNameTwoStep_subset hR ht)
  intro p τ hp q hq _
  exact (pair_mem_normalizedNameTwoStep _ _ _ _ _ _ _).mpr
    ⟨hq, ((pair_mem_normalizedNameTwoStep _ _ _ _ _ _ _).mp hp).2⟩

theorem normalizedTwoStep_prefixGeneric_eq {P R one δ Q S : V} [IsOrdinal δ] {G : Set V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hG : IsExternalForcingFilter (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G) :
    forcingProjectionGeneric P R (nameTwoStepPrefix (boundedNameTwoStep P R δ Q)) G =
    forcingProjectionGeneric P R (nameTwoStepPrefix (normalizedNameTwoStep P R one δ Q))
      {z | z ∈ G ∧ z ∈ normalizedNameTwoStep P R one δ Q} := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨hp, z, hzG, hzp⟩
    have hz := hG.1 z hzG
    have hn := (guardedTwoStepCode_generic_iff hR ht hδ hP hI hG hz).mpr hzG
    refine ⟨hp, guardedTwoStepCode P R one z, hn, ?_⟩
    rw [nameTwoStepPrefix_value hn.2, guardedTwoStepCode_prefix]
    rwa [nameTwoStepPrefix_value hz] at hzp
  · rintro ⟨hp, z, hz, hzp⟩
    refine ⟨hp, z, hz.1, ?_⟩
    rw [nameTwoStepPrefix_value (hG.1 z hz.1)]
    rwa [nameTwoStepPrefix_value hz.2] at hzp

end ZFVP
