import ZFVP.ModelTheory.WoodinSparseRankAgreement
import ZFVP.ModelTheory.WoodinSparseFiniteRankLift
import ZFVP.ModelTheory.FiniteRankLiftGraphRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hδ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
variable (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
  (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
  (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
    (hierarchy (ordinalAdd δ (ω : V))) e)
  (hP : e ‘ (woodinSparseFixedPointContext hΩ hAC hG hγ).P =
    (woodinSparseFixedPointContext hΩ hAC hG hδ).P)
  (hg : ∀ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hγ).G,
    e ‘ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hδ).G)
local notation "L" => woodinSparseFixedPointContext_finiteRankLiftData hΩ hAC hG hγ hδ hfixγ hfixδ he hP hg
local notation "r" => woodinSparseFixedPointContext_between_retraction hΩ hAC hG hγ hδ hγδ
local notation "ab" => woodinSparseFixedPointContext_between_generic_iff hΩ hAC hG hγ hδ hγδ
local notation "j" => woodinSparseFixedPointContext_inclusion hΩ hAC hG hδ

noncomputable def woodinSparseRestrictedLiftGraph : (E).Model := (j) ((L).graph (r))

theorem woodinSparseRestrictedLiftGraph_mem :
    woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg ∈ hierarchy ((E).check Ω) := by
  have hh := (L).graph_mem_larger_rank_in_extension (r) hΩ.inaccessible.rankCriterion.2.2.1 hγ hδ (j)
  rwa [woodinSparseFixedPointContext_inclusion_check] at hh

theorem woodinSparseRestrictedLiftGraph_domain :
    (j) (domain ((L).graph (r))) = hierarchy ((E).check γ) := by
  rw [(L).graph_domain_eq_rank_image (r) (ab)]
  change (j) (woodinSparseFixedPointContext_between hΩ hAC hG hγ hδ hγδ
    (hierarchy ((A).check γ))) = _
  rw [woodinSparseFixedPointContext_inclusion_between,
    woodinSparseFixedPointContext_inclusion_hierarchy]

theorem woodinSparseRestrictedLiftGraph_codedElementary :
    IsCodedMembershipEmbedding (hierarchy ((E).check γ)) (hierarchy ((E).check δ))
      (woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg) := by
  have hone : (A).one = (B).one := (woodinSparseFixedPointContext_top hΩ hAC hG hγ).trans
    (woodinSparseFixedPointContext_top hΩ hAC hG hδ).symm
  have hh := (L).graph_codedElementary_in_extension (r) (ab) hone (j)
  rw [woodinSparseRestrictedLiftGraph_domain hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg,
    woodinSparseFixedPointContext_inclusion_hierarchy] at hh
  exact hh

theorem woodinSparseRestrictedLiftGraph_value (τ : ForcingName (A).P) (hτ : τ.val ∈ hierarchy γ) :
    (woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg) ‘
        (woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ ((A).ofName τ)) =
      (j) ((B).ofName ((L).imageName τ hτ)) := by
  have hh := congrArg (fun x ↦ (j) x) ((L).graph_value (r) (ab) τ hτ)
  rw [(j).map_value_total] at hh
  have hs : (j) ((B).ofName ⟨τ.val, τ.property.mono (r).inclusion⟩) =
      woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ ((A).ofName τ) :=
    woodinSparseFixedPointContext_inclusion_between hΩ hAC hG hγ hδ hγδ ((A).ofName τ)
  rw [hs] at hh
  exact hh

theorem woodinSparseFixedPointContext_exists_restricted_internalLift
    (hγδ : γ ∈ δ)
    (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
    (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd δ (ω : V))) e)
    (hP : e ‘ (A).P = (B).P) (hg : ∀ p ∈ (A).G, e ‘ p ∈ (B).G) :
    ∃ g ∈ hierarchy ((E).check Ω),
      IsCodedMembershipEmbedding (hierarchy ((E).check γ)) (hierarchy ((E).check δ)) g := by
  exact ⟨woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg,
    woodinSparseRestrictedLiftGraph_mem hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg,
    woodinSparseRestrictedLiftGraph_codedElementary hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg⟩

end ZFVP
