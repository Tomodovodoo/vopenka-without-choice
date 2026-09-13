import ZFVP.ModelTheory.ForcingColumnComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance successorForcingLift_definable : ℒₛₑₜ-function₃[V] successorForcingLift := by
  have hd : ℒₛₑₜ-relation₄ (fun g C A L : V ↦ ∀ z, z ∈ g ↔ ∃ a ∈ C ×ˢ A,
    z = ⟨a, successorForcingLiftValue L (kpair.π₁ a) (kpair.π₂ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = successorForcingLift (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [successorForcingLift, mem_definableGraph_iff]

noncomputable def forcingTwoStepLiftColumn (θ D P M : V) : V :=
  definableGraph θ (fun i ↦ successorForcingLift D (P ‘ i) (M ‘ i)) (by
    apply Language.DefinableFunction₃.comp (F := successorForcingLift) <;> definability)

theorem forcingTwoStepLiftColumn_value {θ D P M i a b : V}
    (hi : i ∈ θ) (ha : a ∈ D) (hb : b ∈ P ‘ i) :
    ((forcingTwoStepLiftColumn θ D P M) ‘ i) ‘ ⟨a, b⟩ₖ = successorForcingLiftValue (M ‘ i) a b := by
  rw [forcingTwoStepLiftColumn, value_definableGraph _ _ _ hi, successorForcingLift_value ha hb]

theorem forcingComposeProjectionColumn_twoStep_value {θ P C T ρ i Q S t one a : V}
    (hi : i ∈ θ) (hm : ρ ‘ i ∈ (P ‘ i) ^ C)
    (hT : IsForcingPreorder C T) (htop : IsForcingTop C T one)
    (hQ : IsForcingIterand C T Q S t) (ha : a ∈ twoStepConditions C T Q t) :
    ((forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q t)) ‘ i) ‘ a =
      (ρ ‘ i) ‘ (kpair.π₁ a) := by
  rw [forcingComposeProjectionColumn_value hi,
    value_compose_of_mem_function (twoStep_projection hT htop hQ).maps hm ha,
    twoStepProjection_value ha]

theorem IsCoherentForcingLiftColumn.twoStep {θ P R π L C T ρ M Q S t one : V}
    (c : IsCoherentForcingLiftColumn θ P R π L C T ρ M)
    (hm : ∀ i ∈ θ, ρ ‘ i ∈ (P ‘ i) ^ C)
    (hT : IsForcingPreorder C T) (htop : IsForcingTop C T one)
    (hQ : IsForcingIterand C T Q S t) :
    IsCoherentForcingLiftColumn θ P R π L (twoStepConditions C T Q t) (twoStepOrder C T Q S t)
      (forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q t))
      (forcingTwoStepLiftColumn θ (twoStepConditions C T Q t) P M) := by
  have base {a : V} (ha : a ∈ twoStepConditions C T Q t) : kpair.π₁ a ∈ C := by
    simpa only [twoStepProjection_value ha] using function_value_mem (twoStep_projection hT htop hQ).maps ha
  constructor
  · intro i hi a ha b hb hle
    rw [forcingComposeProjectionColumn_twoStep_value hi (hm i hi) hT htop hQ ha] at hle
    rw [forcingTwoStepLiftColumn_value hi ha hb, forcingComposeProjectionColumn_value hi]
    exact successorForcingLift_lift hT htop hQ (hm i hi) (c.lift i hi) ha hb hle
  · intro i hi j hj hij a ha b hb hle
    rw [forcingComposeProjectionColumn_twoStep_value hi (hm i hi) hT htop hQ ha] at hle
    have hl := successorForcingLift_lift hT htop hQ (hm i hi) (c.lift i hi) ha hb hle
    rw [forcingTwoStepLiftColumn_value hi ha hb,
      forcingComposeProjectionColumn_twoStep_value hj (hm j hj) hT htop hQ hl.1,
      forcingComposeProjectionColumn_twoStep_value hj (hm j hj) hT htop hQ ha]
    apply successorForcingLift_commute
    exact c.commute i hi j hj hij _ (base ha) b hb hle

end ZFVP
