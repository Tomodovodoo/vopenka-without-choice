import ZFVP.ModelTheory.WoodinRecodedStageRules
import ZFVP.ModelTheory.WoodinRecodedSuccessorLift
import ZFVP.ModelTheory.WoodinRecodedInverseLift
import ZFVP.ModelTheory.WoodinRecodedDirectLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRecodedStage_successor_lift {Ω k i q b : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hi : i ∈ succ k)
    (hq : q ∈ (forcingCodeP (woodinRecodedStageCode (succ k))) ‘ (succ k))
    (hb : b ∈ (forcingCodeP (woodinRecodedPrefixCode (succ k))) ‘ i)
    (hle : ⟨b, ((forcingCodeπ (woodinRecodedStageCode (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (woodinRecodedPrefixCode (succ k))) ‘ i) :
    ((forcingCodeL (woodinRecodedStageCode (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨q, b⟩ₖ =
      ⟨((forcingCodeL (woodinRecodedPrefixCode (succ k))) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ q, b⟩ₖ, kpair.π₂ q⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hk0 := hsub k (mem_succ_self k)
  have hd := (woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk0).1
  have hQrank : (woodinRecodingCarriers (woodinRecodingHistory (succ k))) ‘ k ∈
      hierarchy (woodinNormalizedSuccessorCutoff k) := by
    rw [(woodinRecodingHistory_values (mem_succ_self k)).1]
    apply (woodinRecodingRec_correct hΩ hAC k hk0).2.2 _ hd
    rw [woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hk0]
    exact woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  rw [woodinRecodedStageCode_successor] at hq hle ⊢
  rw [woodinRecodedSuccessorNext_carrier_order.1] at hq
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeP_code] at hb
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeR_code] at hle
  exact woodinRecodedSuccessorNext_lift hΩ hAC hk (woodinRecodedPrefix_family hΩ hAC hsub)
    (woodinRecodedPrefix_preorders hΩ hAC hsub)
    (woodinRecodingHistory_tables (succ k)).1 (woodinRecodingHistory_tables (succ k)).2.1 hQrank hi hq hb hle

theorem woodinRecodedStage_inverse_lift {Ω θ i q b : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hi : i ∈ θ) (hq : q ∈ (forcingCodeP (woodinRecodedStageCode θ)) ‘ θ)
    (hb : b ∈ (forcingCodeP (woodinRecodedPrefixCode θ)) ‘ i)
    (hle : ⟨b, ((forcingCodeπ (woodinRecodedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (woodinRecodedPrefixCode θ)) ‘ i) :
    ((forcingCodeL (woodinRecodedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ ⟨q, b⟩ₖ =
      ⟨forcingThreadSplice θ (forcingCodeπ (woodinRecodedPrefixCode θ))
          (forcingCodeL (woodinRecodedPrefixCode θ)) (kpair.π₁ q) i b, kpair.π₂ q⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hd := (woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn).2.1
  have hQrank : ∀ j ∈ θ, (woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ j ∈
      hierarchy (woodinNormalizedInverseCutoff θ) := by
    intro j hj
    rw [(woodinRecodingHistory_values hj).1]
    apply (woodinRecodingRec_correct hΩ hAC j (hsub j hj)).2.2 _ hd
    rw [woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
    exact woodinIterationActualCardinal_increasing hΩ hAC hθ hj
  rw [woodinRecodedStageCode_inverse h0 hlim hn] at hq hle ⊢
  rw [woodinRecodedInverseNext_carrier_order.1] at hq
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeP_code] at hb
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeR_code] at hle
  exact woodinRecodedInverseNext_lift hΩ hAC hθ h0 hlim hn (woodinRecodedPrefix_family hΩ hAC hsub)
    (woodinRecodedPrefix_preorders hΩ hAC hsub)
    (woodinRecodingHistory_tables θ).1 (woodinRecodingHistory_tables θ).2.1 hQrank hi hq hb hle

theorem woodinRecodedStage_direct_lift {Ω θ i q b : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hi : i ∈ θ) (hq : q ∈ (forcingCodeP (woodinRecodedStageCode θ)) ‘ θ)
    (hb : b ∈ (forcingCodeP (woodinRecodedPrefixCode θ)) ‘ i)
    (hle : ⟨b, ((forcingCodeπ (woodinRecodedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (woodinRecodedPrefixCode θ)) ‘ i) :
    let c := woodinRecodedPrefixCode θ
    ((forcingCodeL (woodinRecodedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ ⟨q, b⟩ₖ =
      (forcingSparseEncode θ c (forcingCodeUniverse c)) ‘
        (forcingThreadSplice θ (forcingCodeπ c) (forcingCodeL c)
          ((forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ q) i b) := by
  rw [woodinRecodedStageCode_direct h0 hlim hn] at hq hle ⊢
  rw [woodinRecodedDirectNext_carrier_order.1] at hq
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeP_code] at hb
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeR_code] at hle
  exact woodinRecodedDirectNext_lift hΩ hAC hθ h0 hlim hn (woodinRecodedPrefix_family hΩ hAC hθ)
    (woodinRecodedPrefix_preorders hΩ hAC hθ)
    (woodinRecodingHistory_tables θ).1 (woodinRecodingHistory_tables θ).2.1 hi hq hb hle

theorem woodinRecodedStage_diagonal_lift {Ω θ q b : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hq : q ∈ (forcingCodeP (woodinRecodedStageCode θ)) ‘ θ)
    (hb : b ∈ (forcingCodeP (woodinRecodedStageCode θ)) ‘ θ)
    (hle : ⟨b, q⟩ₖ ∈ (forcingCodeR (woodinRecodedStageCode θ)) ‘ θ) :
    ((forcingCodeL (woodinRecodedStageCode θ)) ‘ ⟨θ, θ⟩ₖ) ‘ ⟨q, b⟩ₖ = b := by
  have hs := woodinRecodedStageCode_valid hΩ hAC hθ
  have hi := mem_succ_self θ
  have hl := hs.system.lifts.lift θ hi θ hi (subset_refl θ) q hq b hb
    (by simpa only [hs.system.split.projId hi hq] using hle)
  simpa only [hs.system.split.projId hi hl.1] using hl.2.2

end ZFVP
