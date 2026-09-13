import ZFVP.ModelTheory.WoodinSparseFiniteRankLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e π : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hδ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

theorem woodinSparseFixedPointContext_internalLift_in_endpoint
    (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
    (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd δ (ω : V))) e)
    (hP : e ‘ (A).P = (B).P) (hg : ∀ p ∈ (A).G, e ‘ p ∈ (B).G)
    (hπ : IsForcingRetraction (A).P (A).R (B).P (B).R π)
    (hAB : ∀ p, p ∈ (A).G ↔ p ∈ (B).G ∧ p ∈ (A).P)
    (hone : (A).one = (B).one)
    (j : MembershipEndExtension (B).Model (E).Model) :
    ∃ g : (E).Model,
      IsCodedMembershipEmbedding
        (j (ForcingContext.retractionInclusion (A) (B) hπ hAB (hierarchy ((A).check γ))))
        (j (hierarchy ((B).check δ))) g ∧
      ∀ τ : ForcingName (A).P, ∀ hτ : τ.val ∈ hierarchy γ,
        g ‘ (j ((B).ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩)) =
          j ((B).ofName ⟨e ‘ τ.val,
            (woodinSparseFixedPointContext_finiteRankLiftData hΩ hAC hG hγ hδ
              hfixγ hfixδ he hP hg).image_name hτ τ.property⟩) := by
  let L := woodinSparseFixedPointContext_finiteRankLiftData hΩ hAC hG hγ hδ
    hfixγ hfixδ he hP hg
  refine ⟨j (L.graph hπ), ?_, ?_⟩
  · have hh := L.graph_codedElementary_in_extension hπ hAB hone j
    rwa [L.graph_domain_eq_rank_image hπ hAB] at hh
  · intro τ hτ
    rw [← j.map_value_total, L.graph_value hπ hAB τ hτ]
    rfl

end ZFVP
