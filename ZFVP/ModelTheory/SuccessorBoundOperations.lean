import ZFVP.SetTheory.ForcingBoundExtension
import ZFVP.ModelTheory.ForcingColumnFunctions
import ZFVP.ModelTheory.SaturatedTwoStepBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSuccessorBound (C A v b I : V) : V :=
  definableGraph ((C ^ I) ×ˢ A)
    (fun x ↦ twoStepUnionBound I (b ‘ ⟨compose (kpair.π₁ x) v, kpair.π₂ x⟩ₖ) (kpair.π₁ x)) (by
      apply Language.DefinableFunction₃.comp <;> definability)

theorem forcingSuccessorBound_value {C A v b I f p : V} (hf : f ∈ C ^ I) (hp : p ∈ A) :
    (forcingSuccessorBound C A v b I) ‘ ⟨f, p⟩ₖ = twoStepUnionBound I (b ‘ ⟨compose f v, p⟩ₖ) f := by
  rw [forcingSuccessorBound, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hf, hp⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem successorProjection_family_compose {θ P R π E k Q S t one I f j : V}
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hk : k ∈ θ) (hmax : ∀ a ∈ θ, a ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t)
    (hf : f ∈ (twoStepConditions (P ‘ k) (R ‘ k) Q t) ^ I) (hj : j ∈ θ) :
    compose (compose f (twoStepProjection (P ‘ k) (R ‘ k) Q t)) (π ‘ ⟨j, k⟩ₖ) =
      compose f ((successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k) ‘ j) := by
  have hbase := (twoStep_projection hR htop hQ).maps
  have hproj := m.projection j hj k hk (hmax j hj)
  have hcol := (successor_functionalColumn h hk hmax hR htop hQ).projection j hj
  have hg := compose_function hf hbase
  have hleft := compose_function hg hproj
  have hright := compose_function hf hcol
  let := IsFunction.of_mem hleft
  let := IsFunction.of_mem hright
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hleft, domain_eq_of_mem_function hright]
  · intro a ha
    rw [domain_eq_of_mem_function hleft] at ha
    rw [value_compose_of_mem_function hg hproj ha, value_compose_of_mem_function hf hbase ha,
      value_compose_of_mem_function hf hcol ha, twoStepProjection_value (function_value_mem hf ha),
      successorProjectionColumn_value hj (function_value_mem hf ha)]

end ZFVP
