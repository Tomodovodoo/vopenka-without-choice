import ZFVP.ModelTheory.WoodinSparseCertificateInputs
import ZFVP.ModelTheory.SparseOrderTableBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_rank_inaccessible
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsChoicelessInaccessible (rank P) := by
  rw [woodinSparseStageCode_rank_eq hΩ hAC hθ]
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with he | hi
  · subst Ω
    rw [woodinIteration_endpoint_cardinal hΩ hAC]
    exact hΩ.inaccessible
  · exact ((woodinIterationExit hΩ hAC).2.1 θ hi).1.inaccessible θ (mem_succ_self _)

theorem woodinSparseStageCode_canonical_order_certificate {η a : V} [IsOrdinal η] [IsOrdinal a]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hη : ∀ β ∈ η, succ β ∈ η) (h0 : (∅ : V) ∈ hierarchy η) (hP : P ⊆ hierarchy η) :
    boundedSparseOrderCertificateFormula.Evalb
      ![hierarchy (succ η), hierarchy η, P, a, sparseCarrierCutFamily P a,
        sparseCarrierOrderTable P a, sparseCarrierAtomicFamily P (hierarchy η) a] := by
  let := hierarchy_transitive η
  apply sparseOrderCertificate_of_tables
    (fun _ hb ↦ sparseCarrierCutFamily_value hb)
    (fun _ hb ↦ sparseCarrierOrderTable_value hb)
  · intro b hb
    rw [sparseCarrierCutFamily_value hb, sparseCarrierOrderTable_value hb]
    exact sparseCarrierAtomicFamily_spec hb
  · intro b hb
    let := IsOrdinal.of_mem hb
    rw [sparseCarrierCutFamily_value hb, sparseCarrierOrderTable_value hb,
      sparseCarrierAtomicFamily_value hb]
    refine ⟨?_, sparseCarrierOrder_mem_successor hη hP, sparseCarrierAtomicTable_mem_successor hη hP⟩
    rw [hierarchy_succ, mem_power_iff]
    exact fun p hp ↦ hP p (mem_sparseCarrierCut_iff.mp hp).1
  · intro b hb
    let := IsOrdinal.of_mem hb
    exact woodinSparseStageCode_candidate_preorder hΩ hAC hθ b
  · intro b hb p hp
    let := IsOrdinal.of_mem hb
    exact woodinSparseStageCode_coordinate_isName hΩ hAC hθ hp
  · intro b _ p hp
    exact woodinSparseStageCode_certificate_support hΩ hAC hθ hη h0 hP hp b

theorem woodinSparseStageCode_finite_order_certificate
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    let η := rank P
    let a := succ (succ η)
    ∃ C ∈ hierarchy (ordinalAdd η (ω : V)), ∃ O ∈ hierarchy (ordinalAdd η (ω : V)),
      ∃ E ∈ hierarchy (ordinalAdd η (ω : V)),
        boundedSparseOrderCertificateFormula.Evalb ![hierarchy (succ η), hierarchy η, P, a, C, O, E] ∧
          O ‘ (succ η) = R := by
  dsimp only
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have hlim := hη.rankCriterion.2.2.1
  have hP := subset_hierarchy_rank P
  have hb := sparseRecoveryTables_finiteRank hlim hP (subset_refl (succ (succ (rank P))))
  refine ⟨_, hb.1, _, hb.2.1, _, hb.2.2, ?_, ?_⟩
  · apply woodinSparseStageCode_canonical_order_certificate hΩ hAC hθ hlim _ hP
    exact ordinal_subset_hierarchy _ ∅ (hη.regular.2.1 ∅ (by simp))
  · rw [sparseCarrierOrderTable_value (mem_succ_self _)]
    exact woodinSparseStageCode_order_from_carrier hΩ hAC hθ

end ZFVP
