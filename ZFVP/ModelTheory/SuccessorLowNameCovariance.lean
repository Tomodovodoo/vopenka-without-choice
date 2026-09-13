import ZFVP.ModelTheory.SuccessorLowNameFamily
import ZFVP.ModelTheory.FiniteRankLowNameCovariance

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorLowNameSet_eq_lowRankNameSet {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    successorLowNameSet P η = lowRankNameSet P (succ η) := by
  apply mem_ext
  intro τ
  constructor
  · intro hτ
    exact (mem_lowRankNameSet _ _ _).mpr
      ⟨successorLowNameSet_subset_hierarchy hη hP τ hτ, successorLowNameSet_isName hτ⟩
  · intro hτ
    obtain ⟨hτ, hn⟩ := (mem_lowRankNameSet _ _ _).mp hτ
    have hr : rank τ ⊆ η := by
      apply rank_minimal _ _ inferInstance
      rwa [hierarchy_succ, mem_power_iff] at hτ
    apply mem_successorLowNameSet.mpr
    intro z hz
    obtain ⟨σ, p, hp, rfl, hσ⟩ := (forcingName_iff _ _).mp hn z hz
    exact kpair_mem_iff.mpr ⟨(mem_lowRankNameSet _ _ _).mpr
      ⟨(mem_hierarchy_iff_rank_mem _ _).mpr (hr _ (rank_subname_lt hz)), hσ⟩, hp⟩

theorem finiteRankEmbedding_value_successorLowNameSet {η ζ f P Q : V}
    [IsOrdinal η] [IsOrdinal ζ]
    (hη : ∀ β ∈ η, succ β ∈ η) (hζ : ∀ β ∈ ζ, succ β ∈ ζ)
    (hP : P ⊆ hierarchy η) (hQ : Q ⊆ hierarchy ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfP : f ‘ P = Q) (hfη : f ‘ η = ζ) :
    f ‘ (successorLowNameSet P η) = successorLowNameSet Q ζ := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hs : ∀ {β : V}, β ∈ ordinalAdd η (ω : V) → succ β ∈ ordinalAdd η (ω : V) :=
    fun {_} ↦ ordinalAdd_omega_succ_closed η
  have h0 := ordinalAdd_omega_gt η
  have hp : P ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (hs h0)
    rwa [hierarchy_succ, mem_power_iff]
  have hηA : η ∈ hierarchy (ordinalAdd η (ω : V)) := ordinal_subset_hierarchy _ _ h0
  have hηsA : succ η ∈ hierarchy (ordinalAdd η (ω : V)) := ordinal_subset_hierarchy _ _ (hs h0)
  rw [successorLowNameSet_eq_lowRankNameSet hη hP,
    successorLowNameSet_eq_lowRankNameSet hζ hQ,
    limitRankEmbedding_value_lowRankNameSet (fun _ ↦ ordinalAdd_omega_succ_closed η)
      (fun _ ↦ ordinalAdd_omega_succ_closed ζ) he hp (hs h0),
    hfP, he.value_succ hηA hηsA, hfη]

end ZFVP
