import ZFVP.ModelTheory.SchmerlInternalDiamondFusion

/-! Densely below a condition forcing clubhood, a condition appends the
exact decided subset at an index which it forces into the named club. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcesMembershipPattern (P R one τ p X B : V) : Prop :=
  ∀ x ∈ X, (x ∈ B → p ∈ atomicMembership P R (checkName one x) τ) ∧
    (x ∉ B → p ∈ forcingNegation P R (atomicMembership P R (checkName one x) τ))

instance forcesMembershipPattern_definable (P R one τ : V) :
    ℒₛₑₜ-relation₃[V] (ForcesMembershipPattern P R one τ) := by
  unfold ForcesMembershipPattern
  definability

theorem forcesMembershipPattern_mono {P R one τ p q X B : V}
    (hR : IsForcingPreorder P R) (h : ForcesMembershipPattern P R one τ p X B)
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) : ForcesMembershipPattern P R one τ q X B := by
  intro x hx
  exact ⟨fun hb ↦ atomicMembership_mono hR ((h x hx).1 hb) hq hqp,
    fun hb ↦ forcingNegation_mono hR ((h x hx).2 hb) hq hqp⟩

noncomputable def decidedMembershipSet (P R one τ p X : V) : V :=
  {x ∈ X ; p ∈ atomicMembership P R (checkName one x) τ}

theorem decidedMembershipSet_pattern {P R one τ p X : V}
    (h : DecidesMembershipOn P R one τ p X) :
    ForcesMembershipPattern P R one τ p X (decidedMembershipSet P R one τ p X) := by
  intro x hx
  refine ⟨fun hb ↦ (mem_sep_iff.mp hb).2, fun hb ↦ ?_⟩
  exact (mem_union_iff.mp (h x hx)).resolve_left
    (fun hpos ↦ hb (mem_sep_iff.mpr ⟨hx, hpos⟩))

def DiamondGuessCondition (κ τ σ p : V) : Prop :=
  ∃ α ∈ domain p,
    p ∈ atomicMembership (diamondConditions κ) (diamondOrder κ) (checkName ∅ α) σ ∧
    ForcesMembershipPattern (diamondConditions κ) (diamondOrder κ) ∅ τ p α (p ‘ α)

instance diamondGuessCondition_definable (κ τ σ : V) :
    ℒₛₑₜ-predicate[V] (DiamondGuessCondition κ τ σ) := by
  unfold DiamondGuessCondition
  definability

theorem diamond_guesses_denseBelow [Countable V] {κ τ σ base : V}
    (hAC : InternalChoice V) (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hcount : ∀ α ∈ κ, IsInternallyCountable α)
    (hσ : IsForcingName (diamondConditions κ) σ)
    (hbase : ForcesClubName (diamondConditions κ) (diamondOrder κ) ∅ κ σ base) :
    ForcingDenseBelow (diamondConditions κ) (diamondOrder κ)
      {p ∈ diamondConditions κ ; DiamondGuessCondition κ τ σ p} base := by
  refine ⟨sep_subset, fun p hp hpb ↦ ?_⟩
  have hbp := ((pair_mem_reverseInclusionOrder _ _ _).mp hpb).2.2
  obtain ⟨f, hf, hf0, hs⟩ := exists_diamondFusionSequence hAC hκ hω hcount hσ hbase hp hbp
  let q := ⋃ˢ range f
  let α := domain q
  have hq := diamond_chain_union hκ hω hf
  have hdec := diamondFusion_limit_decides hκ hω hf hs
  have hclub := diamondFusion_limit_forces_club hκ hω hσ hbase hf (hf0.symm ▸ hbp) hs
  let B := decidedMembershipSet (diamondConditions κ) (diamondOrder κ) ∅ τ q α
  have hB : B ⊆ α := sep_subset
  let r := insert ⟨α, B⟩ₖ q
  have hr := diamond_append_condition hκ hω hq hB
  have hqr : q ⊆ r := fun z hz ↦ mem_insert.mpr (Or.inr hz)
  have hrq : ⟨r, q⟩ₖ ∈ diamondOrder κ := (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hq, hqr⟩
  let : IsFunction r := diamondCondition_function hr
  have hpair : ⟨α, B⟩ₖ ∈ r := by simp [r]
  have hv : r ‘ α = B := value_eq_of_kpair_mem hpair
  have hguess : DiamondGuessCondition κ τ σ r := by
    refine ⟨α, mem_domain_of_kpair_mem hpair,
      atomicMembership_mono (diamond_poset κ).1 hclub hr hrq, ?_⟩
    rw [hv]
    exact forcesMembershipPattern_mono (diamond_poset κ).1 (decidedMembershipSet_pattern hdec) hr hrq
  refine ⟨r, mem_sep_iff.mpr ⟨hr, hguess⟩, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hp, ?_⟩⟩
  exact subset_trans (hf0 ▸ diamondFusion_union_contains hf (by simp)) hqr

end ZFVP.Schmerl
