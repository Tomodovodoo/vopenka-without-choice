import ZFVP.ModelTheory.BoundedSparseSeedCertificate
import ZFVP.ModelTheory.WoodinSparseFiniteOrderCertificate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "η" => rank P
local notation "A" => hierarchy (ordinalAdd η (ω : V))

theorem woodinSparseStageCode_finite_seed_certificate
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (woodinSeedCardinal : V) ∈ A ∧ ∃ F ∈ A, ∃ W ∈ A, ∃ C ∈ A,
      boundedSparseSeedCertificateFormula.Evalb
        ![P, hierarchy η, succ (∅ : V), F, W, C, woodinSeedCardinal] := by
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  let := hierarchy_transitive η
  have h0 : (∅ : V) ∈ hierarchy η :=
    ordinal_subset_hierarchy _ ∅ (hη.regular.2.1 ∅ (by simp))
  have hW : sparseCoordinatePool P (succ (∅ : V)) ⊆ hierarchy η :=
    sparseCoordinatePool_subset_hierarchy h0 (subset_hierarchy_rank P)
      (fun p hp ↦ (woodinSparseStageCode_sparse hΩ hAC hθ hp).1)
  have hT : ∀ τ ∈ hierarchy η, nameValue ({∅} : V) τ ∈ hierarchy η :=
    fun _ hτ ↦ nameValue_mem_hierarchy hτ
  have hC := sparseFirstCoordinateValues_subset_transitive hW hT
  have hm : (woodinSeedCardinal : V) ⊆ hierarchy η := by
    rw [← woodinSparseStageCode_seed_from_carrier hΩ hAC hθ]
    exact collapseRowIndices_subset_transitive hC
  have hsucc := ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η)
  have hbound (x : V) (hx : x ⊆ hierarchy η) : x ∈ A := by
    apply mem_hierarchy_of_mem_stage hsucc
    rw [hierarchy_succ, mem_power_iff]
    exact hx
  refine ⟨hbound _ hm, canonicalNameValueTable ({∅} : V) (hierarchy η),
    mem_hierarchy_of_mem_stage hsucc (canonicalNameValueTable_mem_successor
      hη.rankCriterion.2.2.1), sparseCoordinatePool P (succ (∅ : V)), hbound _ hW,
    sparseFirstCoordinateValues P, hbound _ hC, ?_⟩
  rw [← woodinSparseStageCode_seed_from_carrier hΩ hAC hθ]
  exact boundedSparseSeedCertificate_canonical hW hT

end ZFVP

