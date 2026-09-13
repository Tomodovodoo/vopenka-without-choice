import ZFVP.ModelTheory.WoodinSuccessorCodeRankAgreement
import ZFVP.ModelTheory.WoodinConstruction
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinActualSuccessorRankThreshold (k η : V) : Prop :=
  IsWoodinSuccessorRankThreshold
    (woodinIterationStage (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) k) η

instance woodinActualSuccessorRankThreshold_definable :
    ℒₛₑₜ-relation[V] IsWoodinActualSuccessorRankThreshold := by
  unfold IsWoodinActualSuccessorRankThreshold
  definability

theorem IsWoodinActualSuccessorRankThreshold.mono {k η β : V} [IsOrdinal β]
    (h : IsWoodinActualSuccessorRankThreshold k η) (hηβ : η ∈ β) :
    IsWoodinActualSuccessorRankThreshold k β :=
  IsWoodinSuccessorRankThreshold.mono h hηβ

theorem woodinActualSuccessorRankThreshold_exists {δ k : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hk : k ∈ δ) :
    ∃ η ∈ δ, IsWoodinActualSuccessorRankThreshold k η := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hk
  have h := ((woodinIterationExit hδ hAC).2.1 k hk).1
  apply hδ.woodinSuccessorRankThreshold_exists
    (h.stage k (mem_succ_self k)) (h.small k (mem_succ_self k))
  simpa only [woodinIterationStage, woodinStageCardinal_code] using h.bounded k (mem_succ_self k)

theorem woodinActualSuccessorRankThreshold_bounded {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hα : α ∈ δ) :
    ∃ η ∈ δ, ∀ k ∈ α, IsWoodinActualSuccessorRankThreshold k η := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hα
  let R : V → V → Prop := fun k η ↦ IsOrdinal η ∧ IsWoodinActualSuccessorRankThreshold k η
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hex : ∀ k ∈ α, ∃ η ∈ hierarchy δ, R k η := by
    intro k hkα
    obtain ⟨η, hη, ht⟩ := woodinActualSuccessorRankThreshold_exists hδ hAC
      (IsOrdinal.toIsTransitive.mem_trans hkα hα)
    let := IsOrdinal.of_mem hη
    exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, ht⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hα) R hR hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro k hkα
  obtain ⟨η, hηb, hord, ht⟩ := hall k hkα
  let := hord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact ht.mono hη

theorem IsWoodinActualSuccessorRankThreshold.agreement {k η ξ : V}
    (h : IsWoodinActualSuccessorRankThreshold k η)
    (hηξ : η ∈ ξ) (hξ : IsChoicelessInaccessible ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ s K t : SetDomain (hierarchy ξ), s.val = kpair.π₁ (woodinIterationRec k) →
      K.val = kpair.π₂ (woodinIterationRec k) → t.val = k →
      (woodinIterationSuccessor t s K).val =
        woodinIterationSuccessor k (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) ∧
      (woodinIterationCardinalNext t s K).val =
        woodinIterationCardinalNext k (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) :=
  IsWoodinSuccessorRankThreshold.code_agreement h hηξ hξ

end ZFVP
