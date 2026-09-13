import ZFVP.ModelTheory.WoodinSparseRestrictedLift
import ZFVP.ModelTheory.FiniteRankLiftCriticalPoint
import ZFVP.ModelTheory.EndExtensionCriticalPoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e κ : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
  (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
  (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
  (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
    (hierarchy (ordinalAdd δ (ω : V))) e)
  (hP : e ‘ (woodinSparseFixedPointContext hΩ hAC hG hγ).P =
    (woodinSparseFixedPointContext hΩ hAC hG hδ).P)
  (hg : ∀ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hγ).G,
    e ‘ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hδ).G)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hδ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "L" => woodinSparseFixedPointContext_finiteRankLiftData hΩ hAC hG hγ hδ hfixγ hfixδ he hP hg
local notation "r" => woodinSparseFixedPointContext_between_retraction hΩ hAC hG hγ hδ hγδ
local notation "ab" => woodinSparseFixedPointContext_between_generic_iff hΩ hAC hG hγ hδ hγδ
local notation "j" => woodinSparseFixedPointContext_inclusion hΩ hAC hG hδ
local notation "g" => woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg

include hfixγ hfixδ he hP hg in
theorem woodinSparseRestrictedLift_top_image : e ‘ (A).one = (B).one := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hierarchy_transitive (ordinalAdd δ (ω : V))
  have h0 := (L).low_mem_allowance (L).one_mem_source
  rw [woodinSparseFixedPointContext_top hΩ hAC hG hγ] at h0
  rw [woodinSparseFixedPointContext_top hΩ hAC hG hγ, woodinSparseFixedPointContext_top hΩ hAC hG hδ]
  exact he.value_empty h0

theorem woodinSparseRestrictedLiftGraph_check {x : V} (hx : x ∈ hierarchy γ) :
    (g) ‘ ((E).check x) = (E).check (e ‘ x) := by
  have hone : (A).one = (B).one := (woodinSparseFixedPointContext_top hΩ hAC hG hγ).trans
    (woodinSparseFixedPointContext_top hΩ hAC hG hδ).symm
  have hh := congrArg (fun z ↦ (j) z) ((L).graph_check (r) (ab) hone
    (woodinSparseRestrictedLift_top_image hΩ hAC hG hγ hδ hfixγ hfixδ he hP hg) hx)
  rw [(j).map_value_total, woodinSparseFixedPointContext_inclusion_check,
    woodinSparseFixedPointContext_inclusion_check] at hh
  exact hh

theorem woodinSparseRestrictedLiftGraph_criticalPoint
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) e κ) (hκγ : κ ∈ γ) :
    IsCriticalPoint (hierarchy ((E).check γ)) (g) ((E).check κ) := by
  have hone : (A).one = (B).one := (woodinSparseFixedPointContext_top hΩ hAC hG hγ).trans
    (woodinSparseFixedPointContext_top hΩ hAC hG hδ).symm
  let := (L).graph_domain_transitive (r)
  have hh := (j).criticalPoint_map ((L).graph_criticalPoint (r) (ab) hκ hκγ hone
    (woodinSparseRestrictedLift_top_image hΩ hAC hG hγ hδ hfixγ hfixδ he hP hg))
  rw [woodinSparseRestrictedLiftGraph_domain hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg,
    woodinSparseFixedPointContext_inclusion_check] at hh
  exact hh

end ZFVP
