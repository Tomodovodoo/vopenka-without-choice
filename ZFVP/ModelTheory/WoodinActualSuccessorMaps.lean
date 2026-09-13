import ZFVP.ModelTheory.WoodinNormalizedSuccessorMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k : V} [IsOrdinal k]

theorem woodinNormalizedStage_successor_code
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    woodinNormalizedStageCode (succ k) =
      forcingNormalizedCode (succ (succ k))
        (woodinIterationSuccessor k (kpair.π₁ (woodinIterationRec k))
          (kpair.π₂ (woodinIterationRec k)))
        (woodinNormalizationSuccessor k (kpair.π₁ (woodinIterationRec k))
          (kpair.π₂ (woodinIterationRec k)) (woodinNormalizationHistory (succ k))) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hx := woodinIterationExit hΩ hAC
  have hpref := woodinIterationPrefix_successor
    (woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1))
  simp only [woodinNormalizedStageCode, woodinIterationRec_successor, kpair.π₁_kpair,
    woodinNormalizationHistory_successor, hpref.1, hpref.2]

theorem woodinNormalizedStage_successor_old_carrier {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hi : i ∈ succ k) :
    (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ i =
      (forcingCodeP (woodinNormalizedStageCode k)) ‘ i := by
  rw [woodinNormalizedStage_successor_code hΩ hAC hk]
  exact woodinNormalizedSuccessor_old_carrier hi

theorem woodinNormalizedStage_successor_projection {i z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hi : i ∈ succ k)
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k)) :
    ((forcingCodeπ (woodinNormalizedStageCode (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ z =
      ((forcingCodeπ (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ z) := by
  rw [woodinNormalizedStage_successor_code hΩ hAC hk] at hz ⊢
  exact woodinNormalizedSuccessor_projection hΩ ((woodinIterationExit hΩ hAC).2.1 k hk).1
    (woodinNormalizationHistory_family hΩ hAC k hk) hi hz

theorem woodinNormalizedStage_successor_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hi : i ∈ succ k) (hp : p ∈ (forcingCodeP (woodinNormalizedStageCode k)) ‘ i) :
    ((forcingCodeE (woodinNormalizedStageCode (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ p =
      ⟨((forcingCodeE (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ p, ∅⟩ₖ := by
  rw [woodinNormalizedStage_successor_code hΩ hAC hk]
  exact woodinNormalizedSuccessor_section hΩ ((woodinIterationExit hΩ hAC).2.1 k hk).1
    (woodinNormalizationHistory_family hΩ hAC k hk) hi hp

theorem woodinNormalizedStage_successor_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hi : i ∈ succ k)
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k))
    (hp : p ∈ (forcingCodeP (woodinNormalizedStageCode k)) ‘ i) :
    ((forcingCodeL (woodinNormalizedStageCode (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨z, p⟩ₖ =
      ⟨((forcingCodeL (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ z, p⟩ₖ,
        kpair.π₂ z⟩ₖ := by
  rw [woodinNormalizedStage_successor_code hΩ hAC hk] at hz ⊢
  exact woodinNormalizedSuccessor_lift hΩ ((woodinIterationExit hΩ hAC).2.1 k hk).1
    (woodinNormalizationHistory_family hΩ hAC k hk) hi hz hp

end ZFVP
