import ZFVP.ModelTheory.FiniteRankInternalForcingTable
import ZFVP.ModelTheory.FiniteRankLowNameCovariance
import ZFVP.Syntax.InternalForcingTableUniqueness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteRankEmbedding_internalForces_sameCode {η ζ f P R D n φ b p : V}
    (hη : IsChoicelessInaccessible η) (hζ : IsChoicelessInaccessible ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfη : f ‘ η = ζ) (hP : P ⊆ hierarchy η)
    (hR : R ∈ hierarchy (ordinalAdd η (ω : V))) (hD : D ⊆ hierarchy η)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n φ b p ↔
      InternalForces (f ‘ P) (f ‘ R) (f ‘ D) n φ (f ‘ b) (f ‘ p) := by
  let := hη.1
  let := hζ.1
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  let := hierarchy_isSequenceSupport hη.2.1 hη.rankCriterion.2.2.1
  let := hierarchy_isSequenceSupport
    (IsOrdinal.toIsTransitive.mem_trans hη.2.1 (ordinalAdd_omega_gt η))
    (fun _ ↦ ordinalAdd_omega_succ_closed η)
  have hU : hierarchy η ∈ hierarchy (ordinalAdd η (ω : V)) := hierarchy_mem (ordinalAdd_omega_gt η)
  have hlow : hierarchy η ⊆ hierarchy (ordinalAdd η (ω : V)) :=
    (hierarchy_transitive _).transitive _ hU
  have hbound (x : V) (hx : x ⊆ hierarchy η) : x ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η))
    rwa [hierarchy_succ, mem_power_iff]
  have hnU : n ∈ hierarchy η := IsCodingSupport.natural_mem hφ.context
  have hφU : φ ∈ hierarchy η := membershipFormulaCode_formula_mem_support hφ
  have hbU := function_mem_sequenceSupport hD hφ.context hb
  have hpU := hP p hp
  have hfn := he.value_natural hφ.context
  have hfφ := he.value_formulaCode hφ
  have hbi : f ‘ b ∈ (f ‘ D) ^ n := by
    simpa only [hfn] using he.value_function (hlow _ hbU) (hlow _ hnU) (hbound _ hD) hb
  have hpi : f ‘ p ∈ f ‘ P := (he.value_mem_iff (hlow _ hpU) (hbound _ hP)).mpr hp
  let T := internalForcingTruthTable P R D
  have hT := inaccessible_internalForcingTruthTable_mem_finite_rank (R := R) hη hP hD
  have ht := internalForcingTruthTable_correct P R D
  have hti := finiteRankEmbedding_internalForcingTruthTable hη hζ he hfη hP hR hD hT ht
  have hcU : ⟨n, φ⟩ₖ ∈ hierarchy η := IsCodingSupport.kpair_closed n hnU φ hφU
  have haU : ⟨b, p⟩ₖ ∈ hierarchy η := IsCodingSupport.kpair_closed b hbU p hpU
  have hzU : ⟨⟨n, φ⟩ₖ, ⟨b, p⟩ₖ⟩ₖ ∈ hierarchy η := IsCodingSupport.kpair_closed _ hcU _ haU
  have hz : f ‘ ⟨⟨n, φ⟩ₖ, ⟨b, p⟩ₖ⟩ₖ = ⟨⟨n, φ⟩ₖ, ⟨f ‘ b, f ‘ p⟩ₖ⟩ₖ := by
    rw [he.value_pair (hlow _ hcU) (hlow _ haU) (hlow _ hzU),
      he.value_pair (hlow _ hnU) (hlow _ hφU) (hlow _ hcU),
      he.value_pair (hlow _ hbU) (hlow _ hpU) (hlow _ haU), hfn, hfφ]
  have hl : ForcingTableHolds T n φ b p ↔ ForcingTableHolds (f ‘ T) n φ (f ‘ b) (f ‘ p) := by
    have hh := he.value_mem_iff (hlow _ hzU) hT
    rw [hz] at hh
    exact hh.symm
  exact (ht.lookup hφ hb hp).symm.trans (hl.trans (hti.lookup hφ hbi hpi))

theorem finiteRankEmbedding_lowInternalForces_sameCode {η ζ f P R n φ b p : V}
    (hη : IsChoicelessInaccessible η) (hζ : IsChoicelessInaccessible ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfη : f ‘ η = ζ) (hP : P ⊆ hierarchy η)
    (hR : R ∈ hierarchy (ordinalAdd η (ω : V)))
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ lowRankNameSet P η ^ n) (hp : p ∈ P) :
    InternalForces P R (lowRankNameSet P η) n φ b p ↔
      InternalForces (f ‘ P) (f ‘ R) (lowRankNameSet (f ‘ P) ζ) n φ (f ‘ b) (f ‘ p) := by
  let := hη.1
  let := hζ.1
  have hPA : P ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η))
    rwa [hierarchy_succ, mem_power_iff]
  have hN := limitRankEmbedding_value_lowRankNameSet
    (fun _ ↦ ordinalAdd_omega_succ_closed η) (fun _ ↦ ordinalAdd_omega_succ_closed ζ)
    he hPA (ordinalAdd_omega_gt η)
  rw [hfη] at hN
  simpa only [hN] using finiteRankEmbedding_internalForces_sameCode hη hζ he hfη hP hR
    (lowRankNameSet_subset P η) hφ hb hp

end ZFVP
