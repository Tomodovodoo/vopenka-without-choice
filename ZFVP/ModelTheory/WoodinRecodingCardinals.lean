import ZFVP.ModelTheory.WoodinRecodedSuccessor
import ZFVP.ModelTheory.WoodinNormalizedInverseCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i k : V}

theorem woodinIterationActualCardinal_increasing [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) (hi : i ∈ θ) :
    (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hx := woodinIterationExit hΩ hAC
  have hh := woodinIterationHistory_of_stages
    (fun j hj ↦ (hx.2.1 j (IsOrdinal.toIsTransitive.mem_trans hj hθ)).1)
  have he := (woodinIterationRec_extends_previous hh hi).2
  have hs := (hx.2.1 θ hθ).1
  have hs' := (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1
  rw [hs'.cardinals.value_of_subset hs.cardinals he (mem_succ_self i)]
  exact hs.increasing i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ) hi

theorem woodinNormalizedSuccessorCutoff_actualCardinal [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    woodinNormalizedSuccessorCutoff k = (kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hx := woodinIterationExit hΩ hAC
  have hh := woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  rw [woodinIterationRec_successor_of_history hh, kpair.π₂_kpair]
  simp only [woodinIterationCardinalNext, forcingFamilyNext_new, woodinSuccessorStep,
    woodinSuccessorAt, woodinStageCardinal_code, woodinIterationStage, woodinStagePoset_code,
    woodinStageOrder_code, woodinStageTop_code]
  exact (woodinNormalizedStage_prefix_cutoff hΩ hAC hk _).symm

theorem woodinNormalizedInverseCutoff_actualCardinal [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinNormalizedInverseCutoff θ = (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  rw [woodinNormalizedInverseCutoff_eq hΩ hAC hθ hz, woodinIterationRec_inverse h0 hlim hn,
    kpair.π₂_kpair, woodinInverseCardinalNext, forcingFamilyNext_new]

end ZFVP
