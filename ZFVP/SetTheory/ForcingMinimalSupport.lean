import ZFVP.SetTheory.ForcingDirectLimitFiltration
import ZFVP.SetTheory.Rank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A stage condition has no presentation by a section from an earlier stage. -/
def IsMinimalSectionPoint (P E k p : V) : Prop :=
  p ∈ P ‘ k ∧ ∀ j ∈ k, ∀ q ∈ P ‘ j, p ≠ (E ‘ ⟨j, k⟩ₖ) ‘ q

instance isMinimalSectionPoint_definable : ℒₛₑₜ-relation₄[V] IsMinimalSectionPoint := by
  unfold IsMinimalSectionPoint
  definability

theorem forcingDirectLimit_least_support {θ P π E U f : V} [IsOrdinal θ]
    (hf : f ∈ forcingDirectLimit θ P π E U) :
    ∃! k, IsLeastOrdinal (IsThreadSupport θ E f) k := by
  obtain ⟨_, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  apply leastOrdinal_existsUnique _ (by definability)
  exact ⟨k, IsOrdinal.of_mem hk.1, hk⟩

theorem minimalSectionPoint_of_least_support {θ P π E U f k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hf : f ∈ forcingInverseLimit θ P π U)
    (hk : IsLeastOrdinal (IsThreadSupport θ E f) k) :
    IsMinimalSectionPoint P E k (f ‘ k) := by
  let := hk.1
  have hp := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk.2.1.1
  refine ⟨hp, ?_⟩
  intro j hj q hq he
  let := IsOrdinal.of_mem hj
  have hjθ : j ∈ θ := IsOrdinal.toIsTransitive.mem_trans hj hk.2.1.1
  have hfj : f = forcingSectionThread θ π E j q := by
    rw [forcingThread_eq_section_of_support h hf hk.2.1 hU, he]
    exact forcingSectionThread_comp h hjθ hk.2.1.1
      (IsOrdinal.toIsTransitive.transitive _ hj) hq hU
  have hjs : IsThreadSupport θ E f j := hfj ▸ forcingSectionThread_support h hjθ hq
  exact mem_irrefl j (hk.2.2 j inferInstance hjs j hj)

theorem least_support_of_minimalSectionPoint {θ P π E U k p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hk : k ∈ θ) (hp : IsMinimalSectionPoint P E k p) :
    IsLeastOrdinal (IsThreadSupport θ E (forcingSectionThread θ π E k p)) k := by
  let := IsOrdinal.of_mem hk
  have hf := forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hp.1 hU)
  refine ⟨inferInstance, forcingSectionThread_support h hk hp.1, ?_⟩
  intro j hj hjs
  let := hj
  rcases IsOrdinal.mem_trichotomy k j with hkj | rfl | hjk
  · exact IsOrdinal.toIsTransitive.transitive _ hkj
  · exact subset_refl _
  · have hq := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 j hjs.1
    have he := hjs.2 k hk (IsOrdinal.toIsTransitive.transitive _ hjk)
    rw [forcingSectionThread_value hk, forcingSectionValue_self h hk hp.1] at he
    exact (hp.2 j hjk _ hq he).elim

theorem minimalSectionPoint_section_injective {θ P π E U k l p q : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hk : k ∈ θ) (hl : l ∈ θ)
    (hp : IsMinimalSectionPoint P E k p) (hq : IsMinimalSectionPoint P E l q)
    (he : forcingSectionThread θ π E k p = forcingSectionThread θ π E l q) :
    k = l ∧ p = q := by
  have hkp := least_support_of_minimalSectionPoint h hU hk hp
  have hlq := least_support_of_minimalSectionPoint h hU hl hq
  rw [he] at hkp
  have hkl : k = l := subset_antisymm (hkp.2.2 l hlq.1 hlq.2.1)
    (hlq.2.2 k hkp.1 hkp.2.1)
  subst l
  refine ⟨rfl, ?_⟩
  have hv := congrArg (fun f : V ↦ f ‘ k) he
  simpa only [forcingSectionThread_value hk, forcingSectionValue_self h hk hp.1,
    forcingSectionValue_self h hk hq.1] using hv

end ZFVP
