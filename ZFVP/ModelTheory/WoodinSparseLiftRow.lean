import ZFVP.ModelTheory.WoodinSparseStageRules
import ZFVP.SetTheory.SparseSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseStageMap (θ : V) : V := kpair.π₂ (kpair.π₂ (woodinSparseRecodingRec θ))

instance woodinSparseStageMap_definable : ℒₛₑₜ-function₁[V] woodinSparseStageMap := by
  unfold woodinSparseStageMap
  definability

theorem woodinSparseStageMap_history {θ i : V} (hi : i ∈ θ) :
    (woodinRecodingMaps (woodinSparseRecodingHistory θ)) ‘ i = woodinSparseStageMap i :=
  (woodinSparseRecodingHistory_values hi).2.2

theorem woodinSparseStageMap_successor (k : V) [IsOrdinal k] :
    woodinSparseStageMap (succ k) = woodinSparseSuccessorMap k (woodinSparsePrefixCode (succ k))
      (woodinRecodingMaps (woodinSparseRecodingHistory (succ k))) := by
  simp only [woodinSparseStageMap, woodinSparseRecodingRec_successor, woodinSparseRecodingSuccessorRow,
    kpair.π₂_kpair]

theorem woodinSparseStageMap_direct {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseStageMap θ = woodinSparseDirectMap θ (woodinSparsePrefixCode θ)
      (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  simp only [woodinSparseStageMap, woodinSparseRecodingRec_direct h0 hlim hn, woodinSparseRecodingDirectRow,
    kpair.π₂_kpair]

theorem woodinSparseStageMap_inverse {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseStageMap θ = woodinSparseCompletedInverseMap θ (woodinSparsePrefixCode θ)
      (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  simp only [woodinSparseStageMap, woodinSparseRecodingRec_inverse h0 hlim hn, woodinSparseRecodingInverseRow,
    kpair.π₂_kpair]

theorem woodinSparseStageMap_isomorphism {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
      (woodinSparseStageMap θ) := by
  rw [(woodinSparseStageCode_row θ).1, (woodinSparseStageCode_row θ).2]
  exact (woodinSparseRecodingRec_correct_le hΩ hAC hθ).1.1

theorem woodinSparseStageMap_sparse {Ω θ p : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hp : p ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    IsSparseFunctionOn (succ (woodinSourceIndex θ)) ((woodinSparseStageMap θ) ‘ p) :=
  woodinSparseStageCode_sparse hΩ hAC hθ (function_value_mem (woodinSparseStageMap_isomorphism hΩ hAC hθ).1 hp)

def IsWoodinSparseLiftRow (θ : V) : Prop :=
  ∀ i ∈ succ θ, ∀ p ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ,
    ∀ b ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ i,
      ⟨b, ((forcingCodeπ (woodinNormalizedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ p⟩ₖ ∈
        (forcingCodeR (woodinNormalizedStageCode θ)) ‘ i →
      (woodinSparseStageMap θ) ‘ (((forcingCodeL (woodinNormalizedStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ ⟨p, b⟩ₖ) =
        sparsePrefixReplace (succ (woodinSourceIndex i)) ((woodinSparseStageMap θ) ‘ p) ((woodinSparseStageMap i) ‘ b)

instance isWoodinSparseLiftRow_definable : ℒₛₑₜ-predicate[V] IsWoodinSparseLiftRow := by
  unfold IsWoodinSparseLiftRow
  definability

theorem woodinSparseStageMap_diagonal_lift {Ω θ p b : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hp : p ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
    (hb : b ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
    (hle : ⟨b, ((forcingCodeπ (woodinNormalizedStageCode θ)) ‘ ⟨θ, θ⟩ₖ) ‘ p⟩ₖ ∈
      (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ) :
    (woodinSparseStageMap θ) ‘ (((forcingCodeL (woodinNormalizedStageCode θ)) ‘ ⟨θ, θ⟩ₖ) ‘ ⟨p, b⟩ₖ) =
      sparsePrefixReplace (succ (woodinSourceIndex θ)) ((woodinSparseStageMap θ) ‘ p) ((woodinSparseStageMap θ) ‘ b) := by
  have hs : IsForcingIterationCode (succ θ) (woodinNormalizedStageCode θ) := by
    let := hΩ.inaccessible.1
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizedStageCode_endpoint_valid hΩ hAC
    · exact woodinNormalizedStageCode_valid hΩ hAC hθ
  have hl := hs.system.lifts.lift θ (mem_succ_self θ) θ (mem_succ_self θ) (subset_refl θ) p hp b hb hle
  have he := hl.2.2
  rw [hs.system.split.projId (mem_succ_self θ) hl.1] at he
  rw [he]
  have hps := woodinSparseStageMap_sparse hΩ hAC hθ hp
  have hbs := woodinSparseStageMap_sparse hΩ hAC hθ hb
  let := hps.1
  let := hbs.1
  exact (sparsePrefixReplace_empty_tail hps.2.1 hbs.2.1).symm

end ZFVP
