import ZFVP.ModelTheory.FiniteRankMembershipSyntax
import ZFVP.ModelTheory.InternalForcingTableTransport
import ZFVP.Syntax.InternalForcingTableBounds
import ZFVP.SetTheory.CanonicalAtomicTruthTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inaccessible_internalForcingTruthTable_mem_successor {η P R D : V}
    (hη : IsChoicelessInaccessible η) (hP : P ⊆ hierarchy η) (hD : D ⊆ hierarchy η) :
    internalForcingTruthTable P R D ∈ hierarchy (succ η) := by
  let := hη.1
  let := hierarchy_isSequenceSupport hη.2.1 hη.rankCriterion.2.2.1
  rw [hierarchy_succ, mem_power_iff]
  exact internalForcingTruthTable_subset_support hP hD

theorem inaccessible_internalForcingTruthTable_mem_finite_rank {η P R D : V}
    (hη : IsChoicelessInaccessible η) (hP : P ⊆ hierarchy η) (hD : D ⊆ hierarchy η) :
    internalForcingTruthTable P R D ∈ hierarchy (ordinalAdd η (ω : V)) := by
  let := hη.1
  exact mem_hierarchy_of_mem_stage (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η))
    (inaccessible_internalForcingTruthTable_mem_successor hη hP hD)

theorem finiteRankEmbedding_internalForcingTruthTable {η ζ f P R D T : V}
    (hη : IsChoicelessInaccessible η) (hζ : IsChoicelessInaccessible ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfη : f ‘ η = ζ) (hP : P ⊆ hierarchy η)
    (hR : R ∈ hierarchy (ordinalAdd η (ω : V))) (hD : D ⊆ hierarchy η)
    (hT : T ∈ hierarchy (ordinalAdd η (ω : V))) (ht : IsInternalForcingTruthTable P R D T) :
    IsInternalForcingTruthTable (f ‘ P) (f ‘ R) (f ‘ D) (f ‘ T) := by
  let := hη.1
  let := hζ.1
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  let := hierarchy_isSequenceSupport hη.2.1 hη.rankCriterion.2.2.1
  let := hierarchy_isSequenceSupport hζ.2.1 hζ.rankCriterion.2.2.1
  have hηδ := ordinalAdd_omega_gt η
  have hs := ordinalAdd_omega_succ_closed η hηδ
  have hU : hierarchy η ∈ hierarchy (ordinalAdd η (ω : V)) := hierarchy_mem hηδ
  have hlow : hierarchy η ⊆ hierarchy (ordinalAdd η (ω : V)) :=
    (hierarchy_transitive _).transitive _ hU
  have hbound (x : V) (hx : x ⊆ hierarchy η) : x ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage hs
    rwa [hierarchy_succ, mem_power_iff]
  have him : f ‘ (hierarchy η) = hierarchy ζ := by
    rw [(limitRankEmbedding_value_hierarchy
      (fun _ ↦ ordinalAdd_omega_succ_closed η) (fun _ ↦ ordinalAdd_omega_succ_closed ζ)
      he inferInstance (ordinal_subset_hierarchy _ _ hηδ)).2, hfη]
  let : IsSequenceSupport (f ‘ (hierarchy η)) := him.symm ▸
    (inferInstance : IsSequenceSupport (hierarchy ζ))
  have hH := mem_hierarchy_of_mem_stage hs
    (canonicalAtomicTruthTable_mem_successor (R := R) hη.rankCriterion.2.2.1 hP)
  exact he.value_internalForcingTruthTable hU (hlow _ IsCodingSupport.omega_mem)
    (hlow _ (inaccessible_membershipFormulaFamily_mem hη))
    (finiteRankEmbedding_value_membershipFamily hη he) (hbound _ hP) hR (hbound _ hD) hH hT
    hP hD (canonicalAtomicTruthTable_spec P R _ (transitive_subnameClosed inferInstance)) ht

end ZFVP
