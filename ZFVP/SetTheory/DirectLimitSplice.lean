import ZFVP.SetTheory.ForcingThreadSplice
import ZFVP.SetTheory.ForcingSectionMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Section-compatible lift operations preserve eventual support. -/
theorem forcingThreadSplice_support {θ P R π E L U f i b k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hk : IsThreadSupport θ E f k) (hik : i ⊆ k)
    (hcompat : ∀ j ∈ θ, k ⊆ j → ∀ a ∈ P ‘ k, ∀ c ∈ P ‘ i,
      ⟨c, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ a, c⟩ₖ =
        (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, c⟩ₖ)) :
    IsThreadSupport θ E (forcingThreadSplice θ π L f i b) k := by
  classical
  refine ⟨hk.1, ?_⟩
  intro j hj hkj
  have hki : k ∉ i := fun hki ↦ mem_irrefl k (hik k hki)
  have hji : j ∉ i := fun hji ↦ mem_irrefl j (hkj j (hik j hji))
  rw [forcingThreadSplice_value hj, forcingThreadSplice_value hk.1]
  simp only [forcingSpliceValue, ite_eq_right hki, ite_eq_right hji]
  rw [hk.2 j hj hkj]
  apply hcompat j hj hkj _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk.1) b hb
  rwa [forcingInverseLimit_project_subset h hf hi hk.1 hik]

theorem forcingThreadSplice_direct_mem {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingDirectLimit θ P π E U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hcompat : ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j → ∀ a ∈ P ‘ k, ∀ c ∈ P ‘ i,
      ⟨c, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ a, c⟩ₖ =
        (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, c⟩ₖ)) :
    forcingThreadSplice θ π L f i b ∈ forcingDirectLimit θ P π E U := by
  obtain ⟨k, hk, hik⟩ := forcingDirectLimit_cofinal_support h hf hi
  have hf' := forcingDirectLimit_subset _ _ _ _ _ _ hf
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨forcingThreadSplice_mem h hL hf' hi hb hle hU, k,
      forcingThreadSplice_support h hf' hi hb hle hk hik
        (fun j hj hkj ↦ hcompat k hk.1 j hj hik hkj)⟩

theorem forcingThreadSplice_coordinate {θ π L f i b j : V}
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingThreadSplice θ π L f i b) ‘ j = (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ := by
  classical
  rw [forcingThreadSplice_value hj]
  exact ite_eq_right (fun hji ↦ mem_irrefl j (hij j hji))

theorem forcingThreadSplice_section {θ P R π E L U i k a b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hi : i ∈ θ) (hk : k ∈ θ) (hik : i ⊆ k) (ha : a ∈ P ‘ k) (hb : b ∈ P ‘ i)
    (hle : ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hcompat : ∀ j ∈ θ, k ⊆ j → ∀ c ∈ P ‘ k, ∀ d ∈ P ‘ i,
      ⟨d, (π ‘ ⟨i, k⟩ₖ) ‘ c⟩ₖ ∈ R ‘ i →
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ c, d⟩ₖ =
        (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨c, d⟩ₖ)) :
    forcingThreadSplice θ π L (forcingSectionThread θ π E k a) i b =
      forcingSectionThread θ π E k ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ) := by
  have hf := forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk ha hU)
  have hfa : (forcingSectionThread θ π E k a) ‘ k = a := by
    rw [forcingSectionThread_value hk, forcingSectionValue_self h hk ha]
  have hbi : ⟨b, (forcingSectionThread θ π E k a) ‘ i⟩ₖ ∈ R ‘ i := by
    rw [← forcingInverseLimit_project_subset h hf hi hk hik, hfa]
    exact hle
  have hq := (hL.lift i hi k hk hik a ha b hb hle).1
  have hg := forcingThreadSplice_mem h hL hf hi hb hbi hU
  have hgk := forcingThreadSplice_support h hf hi hb hbi
    (forcingSectionThread_support h hk ha) hik hcompat
  apply forcingThread_eq_of_support hg
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hq hU))
    hgk (forcingSectionThread_support h hk hq)
  rw [forcingThreadSplice_coordinate hk hik, hfa,
    forcingSectionThread_value hk, forcingSectionValue_self h hk hq]

end ZFVP
