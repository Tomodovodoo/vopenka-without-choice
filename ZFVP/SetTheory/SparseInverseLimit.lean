import ZFVP.SetTheory.SparseThreadPresentation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingInverseLimit_eq_sparseRestrictionThreads {θ P π U b : V} [IsOrdinal θ]
    (hsp : ∀ i ∈ θ, ∀ p ∈ P ‘ i, IsSparseFunctionOn (b ‘ i) p)
    (hb : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → b ‘ i ⊆ b ‘ j)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ P ‘ j, (π ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (b ‘ i)) :
    forcingInverseLimit θ P π U = sparseRestrictionThreads θ b P U := by
  apply mem_ext
  intro t
  rw [mem_forcingInverseLimit_iff, mem_sparseRestrictionThreads_iff]
  constructor
  · rintro ⟨ht, hp, hc⟩
    refine ⟨ht, fun i hi ↦ ⟨hsp i hi _ (hp i hi), hp i hi⟩, ?_⟩
    have hres {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ∈ j) :
        (t ‘ i) ↾ (b ‘ j) = (t ‘ j) ↾ (b ‘ i) := by
      have hs := hsp i hi _ (hp i hi)
      let := hs.1
      rw [IsFunction.restrict_eq_self _ _ (subset_trans hs.2.1 (hb i hi j hj hij))]
      exact (hc j hj i hij hi).symm.trans (hπ i hi j hj hij _ (hp j hj))
    intro i hi j hj
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
    · exact hres hi hj hij
    · rfl
    · exact (hres hj hi hji).symm
  · rintro ⟨ht, hp, hc⟩
    refine ⟨ht, fun i hi ↦ (hp i hi).2, ?_⟩
    intro j hj i hij hi
    have hs := (hp i hi).1
    let := hs.1
    rw [hπ i hi j hj hij _ (hp j hj).2, ← hc i hi j hj]
    exact IsFunction.restrict_eq_self _ _ (subset_trans hs.2.1 (hb i hi j hj hij))

theorem sparseInverseLimit_isomorphism {θ A P R π U b : V} [IsOrdinal θ]
    (hsp : ∀ i ∈ θ, ∀ p ∈ P ‘ i, IsSparseFunctionOn (b ‘ i) p)
    (hb : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → b ‘ i ⊆ b ‘ j)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ P ‘ j, (π ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (b ‘ i))
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hbA : ∀ i ∈ θ, b ‘ i ⊆ A)
    (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    IsForcingIsomorphism (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) (sparseThreadCarrier θ A b P U)
      (sparseThreadOrder θ b R (sparseThreadCarrier θ A b P U)) (sparseThreadEncode θ b P U) := by
  rw [forcingInverseLimit_eq_sparseRestrictionThreads hsp hb hπ]
  exact sparseThreadEncode_isomorphism hU hbA hcover

end ZFVP
