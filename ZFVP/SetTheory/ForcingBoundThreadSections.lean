import ZFVP.SetTheory.ForcingBoundSectionCompatibility
import ZFVP.SetTheory.ForcingSectionFamilies
import ZFVP.SetTheory.ForcingBoundThreads

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingBoundThread_section {θ P R π E B U i I j f p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hB : IsCoherentForcingBound θ P R π B i I)
    (hc : IsSectionCompatibleForcingBound θ P R π E B i I)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) (hU : ∀ k ∈ θ, P ‘ k ⊆ U)
    (hf : IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f) (hp : p ∈ P ‘ i)
    (hb : ∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
    forcingBoundThread θ π B I (compose f (forcingThreadSection θ P π E j)) i p =
      forcingSectionThread θ π E j ((B ‘ j) ‘ ⟨f, p⟩ₖ) := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hq := hB.bound j hj hij f hf p hp hb
  have hleft : IsFunction (forcingBoundThread θ π B I (compose f (forcingThreadSection θ P π E j)) i p) := by
    unfold forcingBoundThread
    infer_instance
  have hright : IsFunction (forcingSectionThread θ π E j ((B ‘ j) ‘ ⟨f, p⟩ₖ)) := by
    unfold forcingSectionThread
    infer_instance
  apply functions_eq_of_domain_values
  · simp only [forcingBoundThread, forcingSectionThread, domain_definableGraph]
  · intro k hk
    simp only [forcingBoundThread, domain_definableGraph] at hk
    let := IsOrdinal.of_mem hk
    rw [forcingBoundThread_value hk, forcingSectionThread_value hk]
    by_cases hki : k ∈ i
    · have hkj : k ∈ j := hij k hki
      simp only [forcingBoundValue, ite_eq_left hki, forcingSectionValue, ite_eq_left hkj]
      have he := h.projComp k hk i hi j hj (IsOrdinal.toIsTransitive.transitive _ hki) hij _ hq.1
      rwa [hq.2.2] at he
    · by_cases hkj : k ∈ j
      · have hik : i ⊆ k := by
          rcases IsOrdinal.mem_trichotomy k i with hki' | rfl | hik
          · exact (hki hki').elim
          · exact subset_refl _
          · exact IsOrdinal.toIsTransitive.transitive _ hik
        have hkj' := IsOrdinal.toIsTransitive.transitive _ hkj
        simp only [forcingBoundValue, ite_eq_right hki, forcingSectionValue, ite_eq_left hkj]
        rw [forcingCoordinateFamily_section_below h m hj hk hkj' hU hf.1]
        exact (hB.commute k hk j hj hik hkj' f hf p hp hb).symm
      · have hjk : j ⊆ k := by
          rcases IsOrdinal.mem_trichotomy k j with hkj' | rfl | hjk
          · exact (hkj hkj').elim
          · exact subset_refl _
          · exact IsOrdinal.toIsTransitive.transitive _ hjk
        simp only [forcingBoundValue, ite_eq_right hki, forcingSectionValue, ite_eq_right hkj]
        rw [forcingCoordinateFamily_section_above h m hj hk hjk hU hf.1]
        exact hc.compatible j hj k hk hij hjk f hf p hp hb

end ZFVP
