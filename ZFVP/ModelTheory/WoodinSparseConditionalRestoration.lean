import ZFVP.ModelTheory.WoodinSparseUniformRestoration
import ZFVP.ModelTheory.WoodinSparseConditionalCriticalLift
import ZFVP.ModelTheory.WoodinSparseEndpointOrdinals
import ZFVP.SetTheory.SmallEmbeddingCriterionCardinal

/-! Actual finite restoration in the selected sparse endpoint, with the two
remaining forcing obligations stated directly: correctness of the selected
stages and relative homogeneity of the actual endpoint forcing.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]
variable {r k : ℕ} {Λ : V} [IsOrdinal Λ]
variable (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel r) Λ)
  (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G)
local notation "hW" => (And.right (And.right (woodinSparse_restorationFacts hΛ)))
local notation "E" => woodinSparseGenericContext hW hAC (subset_refl Λ) hG
local notation "W" => WoodinSparseEndpointModel.RankModel hW hAC hG
local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

/-- The restricted ground embeddings, complete-code capture, actual master
condition, generic adjustment, and internal graph descent yield unbounded
extendibles in the actual ZFC endpoint once these two forcing statements hold. -/
theorem prunedUE_sparseEndpoint_smallEmbedding_unbounded_of_forcing
    (hcorrect : ∀ (θ : V) (hθΛ : θ ∈ Λ) (hθ : Cn r θ), IsWoodinSupercompact θ →
      letI := hθ.ordinal
      Cn (k + 2) (WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθΛ))
    (hhom : ∀ δ ∈ Λ, IsWoodinSupercompact δ →
      ∀ t ∈ P[Λ], ∀ p ∈ P[Λ], ⟨π[δ,Λ] ‘ p, π[δ,Λ] ‘ t⟩ₖ ∈ R[δ] →
        ∃ a, IsForcingAutomorphism P[Λ] R[Λ] a ∧
          (∀ q ∈ P[Λ], π[δ,Λ] ‘ (a ‘ q) = π[δ,Λ] ‘ q) ∧
          ForcingCompatible P[Λ] R[Λ] (a ‘ p) t) :
    ∀ η : W, IsOrdinal η → ∃ δ : W, η ∈ δ ∧ SmallEmbeddingCriterion (k + 1) δ := by
  let := hierarchy_transitive ((E).check Λ)
  intro η hη
  obtain ⟨η₀, hη₀, hηΛ, heη⟩ :=
    WoodinSparseEndpointModel.ordinal_eq_checkedOrdinal hW hAC hG η hη
  let := hη₀
  subst η
  obtain ⟨δ, hδΛ, hηδ, hδE, _, hδW, hstages⟩ :=
    prunedUE_sparseUniformRestrictedStages hΛ hAC hηΛ
  let := hδE.1.1
  refine ⟨WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hδΛ,
    (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hηΛ hδΛ).mpr hηδ, ?_⟩
  intro β hβ
  obtain ⟨β₀, hβ₀, hβΛ, heβ⟩ :=
    WoodinSparseEndpointModel.ordinal_eq_checkedOrdinal hW hAC hG β hβ
  let := hβ₀
  subst β
  obtain ⟨θ, hθΛ, hδθ, hβθ, hθ, hθW, hall⟩ := hstages β₀ hβΛ
  let := hθ.ordinal
  refine ⟨WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθΛ,
    (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hβΛ hθΛ).mpr hβθ,
    hcorrect θ hθΛ hθ hθW, ?_⟩
  intro α hαθ
  have hα : IsOrdinal α := IsOrdinal.of_mem hαθ
  obtain ⟨α₀, hα₀, hαΛ, heα⟩ :=
    WoodinSparseEndpointModel.ordinal_eq_checkedOrdinal hW hAC hG α hα
  let := hα₀
  subst α
  have hα₀θ := (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hαΛ hθΛ).mp hαθ
  obtain ⟨κ, θ', α', J, _, hκθ', hθ'δ, hα'θ', hθ', hθ'W,
    hJ, hcrit, hJκ, hJθ', hJα', hcode, hcap⟩ := hall α₀ hα₀θ
  let := hθ'.ordinal
  let := hcrit.ordinal
  let := IsOrdinal.of_mem hα'θ'
  have hθ'Λ := IsOrdinal.toIsTransitive.mem_trans hθ'δ hδΛ
  have hκΛ := IsOrdinal.toIsTransitive.mem_trans hκθ' hθ'Λ
  have hα'Λ := IsOrdinal.toIsTransitive.mem_trans hα'θ' hθ'Λ
  obtain ⟨g, hgΛ, hg, hcg, hvalues⟩ :=
    (E).woodinSparseSource_exists_criticalLift_of_relativeHomogeneity hW hAC hθΛ
      hJ hcode hcap hJθ' (woodinIteration_endpoint_cardinal hθW hAC)
      hcrit hκθ' hθ'δ hJκ
      (woodinSparseSourceStageCode_row (mem_succ_self Λ)).1.symm
      (woodinSparseSourceStageCode_row (mem_succ_self Λ)).2.symm
      (hhom δ hδΛ hδW)
  let g' : W := ⟨g, hgΛ⟩
  refine ⟨WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hκΛ,
    WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθ'Λ,
    WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hα'Λ, g',
    (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hκΛ hθ'Λ).mpr hκθ',
    (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hθ'Λ hδΛ).mpr hθ'δ,
    (WoodinSparseEndpointModel.checkedOrdinal_mem_iff hW hAC hG hα'Λ hθ'Λ).mpr hα'θ',
    hcorrect θ' hθ'Λ hθ' hθ'W, ?_, ?_, ?_, ?_⟩
  · apply (TransitiveZF.codedMembershipEmbedding_iff (hierarchy ((E).check Λ)) _ _ _).mp
    rw [rank_hierarchy_val _ inferInstance, rank_hierarchy_val _ inferInstance]
    exact hg
  · let := hierarchy_transitive (WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθ'Λ)
    apply (MembershipEndExtension.transitiveSubtype (hierarchy ((E).check Λ))).criticalPoint_iff.mp
    change IsCriticalPoint (hierarchy (WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθ'Λ)).val
      g ((E).check κ)
    rw [rank_hierarchy_val _ inferInstance]
    exact hcg
  · apply Subtype.ext
    rw [TransitiveZF.value_val_total]
    change g ‘ ((E).check κ) = (E).check δ
    rw [hvalues κ (ordinal_subset_hierarchy θ' κ hκθ'), hJκ]
  · apply Subtype.ext
    rw [TransitiveZF.value_val_total]
    change g ‘ ((E).check α') = (E).check α₀
    rw [hvalues α' (ordinal_subset_hierarchy θ' α' hα'θ'), hJα']

/-- The internal graph witnesses constructed above give the extendibility
conclusion by the small-embedding criterion. -/
theorem prunedUE_sparseEndpoint_cnExtendible_unbounded_of_forcing
    (hcorrect : ∀ (θ : V) (hθΛ : θ ∈ Λ) (hθ : Cn r θ), IsWoodinSupercompact θ →
      letI := hθ.ordinal
      Cn (k + 2) (WoodinSparseEndpointModel.checkedOrdinal hW hAC hG hθΛ))
    (hhom : ∀ δ ∈ Λ, IsWoodinSupercompact δ →
      ∀ t ∈ P[Λ], ∀ p ∈ P[Λ], ⟨π[δ,Λ] ‘ p, π[δ,Λ] ‘ t⟩ₖ ∈ R[δ] →
        ∃ a, IsForcingAutomorphism P[Λ] R[Λ] a ∧
          (∀ q ∈ P[Λ], π[δ,Λ] ‘ (a ‘ q) = π[δ,Λ] ‘ q) ∧
          ForcingCompatible P[Λ] R[Λ] (a ‘ p) t) :
    ∀ η : W, IsOrdinal η → ∃ δ : W, η ∈ δ ∧ IsCnExtendible (k + 1) δ := by
  intro η hη
  obtain ⟨δ, hηδ, hδ⟩ :=
    prunedUE_sparseEndpoint_smallEmbedding_unbounded_of_forcing hΛ hAC hG hcorrect hhom η hη
  exact ⟨δ, hηδ, hδ.cnExtendible⟩

end ZFVP
