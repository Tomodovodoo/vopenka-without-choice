import ZFVP.ModelTheory.SuccessorBoundOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingComposeProjectionColumn (θ ρ v : V) : V :=
  definableGraph θ (fun j ↦ compose v (ρ ‘ j)) (by definability)

theorem forcingComposeProjectionColumn_value {θ ρ v j : V} (hj : j ∈ θ) :
    (forcingComposeProjectionColumn θ ρ v) ‘ j = compose v (ρ ‘ j) :=
  value_definableGraph _ _ _ hj

/-- A second forcing transports a bound column without requiring a last old index. -/
theorem IsCoherentForcingBoundColumn.twoStep {θ P R B C T ρ M i I Q S t one : V}
    (c : IsCoherentForcingBoundColumn θ P R B C T ρ M i I) (hi : i ∈ θ)
    (hm : ∀ j ∈ θ, ρ ‘ j ∈ (P ‘ j) ^ C)
    (hT : IsForcingPreorder C T) (htop : IsForcingTop C T one)
    (hQ : IsForcingIterand C T Q S t)
    (hU : ∀ f, IsForcingDirectedFamily (twoStepConditions C T Q t) (twoStepOrder C T Q S t) I f →
      ∀ q ∈ C, (∀ a ∈ I, ⟨q, kpair.π₁ (f ‘ a)⟩ₖ ∈ T) →
      twoStepUnionBound I q f ∈ twoStepConditions C T Q t ∧
        ∀ a ∈ I, ⟨twoStepUnionBound I q f, f ‘ a⟩ₖ ∈ twoStepOrder C T Q S t) :
    IsCoherentForcingBoundColumn θ P R B (twoStepConditions C T Q t) (twoStepOrder C T Q S t)
      (forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q t))
      (forcingSuccessorBound (twoStepConditions C T Q t) (P ‘ i) (twoStepProjection C T Q t) M I) i I := by
  let D := twoStepConditions C T Q t
  let U := twoStepOrder C T Q S t
  let v := twoStepProjection C T Q t
  let ρ' := forcingComposeProjectionColumn θ ρ v
  have hv : IsForcingProjection C T D U v := twoStep_projection hT htop hQ
  have hb' {f p : V} (hf : IsForcingDirectedFamily D U I f)
      (hb : ∀ a ∈ I, ⟨p, (ρ' ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      ∀ a ∈ I, ⟨p, (ρ ‘ i) ‘ ((compose f v) ‘ a)⟩ₖ ∈ R ‘ i := by
    intro a ha
    rw [value_compose_of_mem_function hf.1 hv.maps ha]
    simpa only [ρ', forcingComposeProjectionColumn_value hi,
      value_compose_of_mem_function hv.maps (hm i hi) (function_value_mem hf.1 ha)] using hb a ha
  have hbound {f p : V} (hf : IsForcingDirectedFamily D U I f) (hp : p ∈ P ‘ i)
      (hb : ∀ a ∈ I, ⟨p, (ρ' ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      twoStepUnionBound I (M ‘ ⟨compose f v, p⟩ₖ) f ∈ D ∧
        ∀ a ∈ I, ⟨twoStepUnionBound I (M ‘ ⟨compose f v, p⟩ₖ) f, f ‘ a⟩ₖ ∈ U := by
    have hh := c.bound _ (hf.map hv.maps hv.monotone) p hp (hb' hf hb)
    apply hU f hf _ hh.1
    intro a ha
    simpa only [value_compose_of_mem_function hf.1 hv.maps ha, v,
      twoStepProjection_value (function_value_mem hf.1 ha)] using hh.2.1 a ha
  constructor
  · intro f hf p hp hb
    rw [forcingSuccessorBound_value hf.1 hp]
    have hu := hbound hf hp hb
    refine ⟨hu.1, hu.2, ?_⟩
    rw [forcingComposeProjectionColumn_value hi,
      value_compose_of_mem_function hv.maps (hm i hi) hu.1,
      twoStepProjection_value hu.1]
    simp only [twoStepUnionBound, kpair.π₁_kpair]
    exact (c.bound _ (hf.map hv.maps hv.monotone) p hp (hb' hf hb)).2.2
  · intro j hj hij f hf p hp hb
    rw [forcingSuccessorBound_value hf.1 hp, forcingComposeProjectionColumn_value hj,
      value_compose_of_mem_function hv.maps (hm j hj) (hbound hf hp hb).1,
      twoStepProjection_value (hbound hf hp hb).1]
    simp only [twoStepUnionBound, kpair.π₁_kpair]
    rw [← graph_compose_assoc]
    exact c.commute j hj hij _ (hf.map hv.maps hv.monotone) p hp (hb' hf hb)

end ZFVP
