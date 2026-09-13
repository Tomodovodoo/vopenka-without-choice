import ZFVP.ModelTheory.ForcingRecodedSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIsomorphism.target_preorder {P R Q S f : V}
    (hf : IsForcingIsomorphism P R Q S f) (hR : IsForcingPreorder P R) (hS : S ⊆ Q ×ˢ Q) :
    IsForcingPreorder Q S := by
  refine ⟨hS, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := hf.surjective q hq
    exact (hf.2.2.2 p hp p hp).mp (hR.2.1 p hp)
  · intro a ha b hb c hc hab hbc
    obtain ⟨p, hp, rfl⟩ := hf.surjective a ha
    obtain ⟨q, hq, rfl⟩ := hf.surjective b hb
    obtain ⟨r, hr, rfl⟩ := hf.surjective c hc
    exact (hf.2.2.2 p hp r hr).mp
      (hR.2.2 p hp q hq r hr ((hf.2.2.2 p hp q hq).mpr hab) ((hf.2.2.2 q hq r hr).mpr hbc))

variable {θ s C Q T m A B f : V}

theorem forcingRecoded_next_family
    (hP : ∀ i ∈ θ, (forcingCodeP C) ‘ i = (forcingCodeP s) ‘ i)
    (hR : ∀ i ∈ θ, (forcingCodeR C) ‘ i = (forcingCodeR s) ‘ i)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hf : IsForcingIsomorphism ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) A B f) :
    ∀ i ∈ succ θ, IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i)
      ((forcingFamilyNext θ Q A) ‘ i) ((forcingFamilyNext θ T B) ‘ i) ((forcingFamilyNext θ m f) ‘ i) := by
  intro i hi
  rcases mem_succ_iff.mp hi with rfl | hi
  · simpa only [forcingFamilyNext_new] using hf
  · rw [forcingFamilyNext_old hi, forcingFamilyNext_old hi, forcingFamilyNext_old hi, hP i hi, hR i hi]
    exact hm i hi

theorem forcingRecoded_next_code
    (hs : IsForcingIterationCode (succ θ) C)
    (hP : ∀ i ∈ θ, (forcingCodeP C) ‘ i = (forcingCodeP s) ‘ i)
    (hR : ∀ i ∈ θ, (forcingCodeR C) ‘ i = (forcingCodeR s) ‘ i)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hf : IsForcingIsomorphism ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) A B f)
    (hB : B ⊆ A ×ˢ A) :
    IsForcingIterationCode (succ θ) (forcingRecodedCode (succ θ) C
      (forcingFamilyNext θ Q A) (forcingFamilyNext θ T B) (forcingFamilyNext θ m f)) := by
  apply forcingRecoded_code hs (forcingRecoded_next_family hP hR hm hf) ?_
    (forcingFamilyNext_table _ _ _) (forcingFamilyNext_table _ _ _)
  intro i hi
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    simp only [forcingFamilyNext_new]
    exact hf.target_preorder (hs.system.order.preorder θ (mem_succ_self θ)) hB
  · rw [forcingFamilyNext_old hi, forcingFamilyNext_old hi]
    exact hT i hi

end ZFVP
