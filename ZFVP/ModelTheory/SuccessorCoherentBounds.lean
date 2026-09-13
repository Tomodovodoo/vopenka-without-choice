import ZFVP.ModelTheory.SuccessorBoundOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successor_coherentBoundColumn {θ P R π E B i k Q S t one I : V}
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hB : IsCoherentForcingBound θ P R π B i I) (hi : i ∈ θ) (hk : k ∈ θ)
    (hmax : ∀ j ∈ θ, j ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t)
    (hU : ∀ f, IsForcingDirectedFamily (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S t) I f → ∀ q ∈ P ‘ k,
      (∀ a ∈ I, ⟨q, kpair.π₁ (f ‘ a)⟩ₖ ∈ R ‘ k) →
      twoStepUnionBound I q f ∈ twoStepConditions (P ‘ k) (R ‘ k) Q t ∧
      ∀ a ∈ I, ⟨twoStepUnionBound I q f, f ‘ a⟩ₖ ∈ twoStepOrder (P ‘ k) (R ‘ k) Q S t) :
    IsCoherentForcingBoundColumn θ P R B (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S t)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k)
      (forcingSuccessorBound (twoStepConditions (P ‘ k) (R ‘ k) Q t) (P ‘ i)
        (twoStepProjection (P ‘ k) (R ‘ k) Q t) (B ‘ k) I) i I := by
  let C := twoStepConditions (P ‘ k) (R ‘ k) Q t
  let T := twoStepOrder (P ‘ k) (R ‘ k) Q S t
  let v := twoStepProjection (P ‘ k) (R ‘ k) Q t
  let ρ := successorProjectionColumn θ C π k
  have hbase : IsForcingProjection (P ‘ k) (R ‘ k) C T v := twoStep_projection hR htop hQ
  have hpb {f p : V} (hf : IsForcingDirectedFamily C T I f)
      (hb : ∀ a ∈ I, ⟨p, (ρ ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      ∀ a ∈ I, ⟨p, (π ‘ ⟨i, k⟩ₖ) ‘ ((compose f v) ‘ a)⟩ₖ ∈ R ‘ i := by
    intro a ha
    rw [value_compose_of_mem_function hf.1 hbase.maps ha,
      twoStepProjection_value (function_value_mem hf.1 ha)]
    simpa only [ρ, successorProjectionColumn_value hi (function_value_mem hf.1 ha)] using hb a ha
  have hbound {f p : V} (hf : IsForcingDirectedFamily C T I f) (hp : p ∈ P ‘ i)
      (hb : ∀ a ∈ I, ⟨p, (ρ ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      twoStepUnionBound I ((B ‘ k) ‘ ⟨compose f v, p⟩ₖ) f ∈ C ∧
      ∀ a ∈ I, ⟨twoStepUnionBound I ((B ‘ k) ‘ ⟨compose f v, p⟩ₖ) f, f ‘ a⟩ₖ ∈ T := by
    have hh := hB.bound k hk (hmax i hi) _ (hf.map hbase.maps hbase.monotone) p hp (hpb hf hb)
    apply hU f hf _ hh.1
    intro a ha
    simpa only [value_compose_of_mem_function hf.1 hbase.maps ha, v,
      twoStepProjection_value (function_value_mem hf.1 ha)] using hh.2.1 a ha
  constructor
  · intro f hf p hp hb
    rw [forcingSuccessorBound_value hf.1 hp]
    have hh := hbound hf hp hb
    refine ⟨hh.1, hh.2, ?_⟩
    rw [successorProjectionColumn_value hi hh.1]
    simp only [twoStepUnionBound, kpair.π₁_kpair]
    exact (hB.bound k hk (hmax i hi) _ (hf.map hbase.maps hbase.monotone) p hp (hpb hf hb)).2.2
  · intro j hj hij f hf p hp hb
    rw [forcingSuccessorBound_value hf.1 hp,
      successorProjectionColumn_value hj (hbound hf hp hb).1]
    have hc := hB.commute j hj k hk hij (hmax j hj) _
      (hf.map hbase.maps hbase.monotone) p hp (hpb hf hb)
    rw [successorProjection_family_compose h m hk hmax hR htop hQ hf.1 hj] at hc
    simpa only [twoStepUnionBound, kpair.π₁_kpair] using hc

end ZFVP
