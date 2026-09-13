import ZFVP.ModelTheory.ForcingQuotientSeparation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingIntersection {P : V} (R : V) (τ σ : ForcingName P) : ForcingName P :=
  forcingSelected R τ (fun ν ↦ atomicMembership P R ν σ.val) (by definability)

theorem forcingQuotient_intersectionName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ σ : ForcingName P)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingIntersection R τ σ) ↔
      x ∈ forcingQuotientMk P R G hR hG.1 τ ∧ x ∈ forcingQuotientMk P R G hR hG.1 σ := by
  unfold IsExternalForcingGeneric at hG
  unfold forcingIntersection
  rw [forcingQuotient_selectedName P R G hR hG τ _ _
    (fun ν _ ↦ (atomicMembership_regular hR ν σ.val).2.1)]
  constructor
  · rintro ⟨ν, s, hsG, hs, rfl, hF⟩
    exact ⟨(forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr ⟨ν, s, hsG, hs, rfl⟩,
      (forcingQuotientMk_mem_iff P R G hR hG.1 _ _).mpr hF⟩
  · rintro ⟨hx, hσ⟩
    obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
    obtain ⟨ν, s, hsG, hs, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    refine ⟨ν, s, hsG, hs, he, (forcingQuotientMk_mem_iff P R G hR hG.1 _ _).mp ?_⟩
    rwa [he] at hσ

theorem forcingQuotient_boundedRepresentative (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P)
    (x : ForcingQuotient P R G hR hG.1)
    (hx : ∀ z, z ∈ x → z ∈ forcingQuotientMk P R G hR hG.1 τ) :
    ∃ ρ : ForcingName P, ρ.val ⊆ domain τ.val ×ˢ P ∧ forcingQuotientMk P R G hR hG.1 ρ = x := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  refine ⟨forcingIntersection R τ σ, ?_, ?_⟩
  · exact forcingSelectedName_subset P R τ.val (fun ν ↦ atomicMembership P R ν σ.val) (by definability)
  apply forcingQuotient_extensionality P R G hR hG
  intro z
  rw [forcingQuotient_intersectionName P R G hR hG]
  exact ⟨And.right, fun hz ↦ ⟨hx z hz, hz⟩⟩

end ZFVP
