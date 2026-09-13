import ZFVP.SetTheory.ForcingDirectLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Algebraic laws of the projections and sections, including diagonal maps. -/
structure IsSplitForcingSystem (θ P π E : V) : Prop where
  projMaps : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ j,
    (π ‘ ⟨i, j⟩ₖ) ‘ p ∈ P ‘ i)
  secMaps : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
    (E ‘ ⟨i, j⟩ₖ) ‘ p ∈ P ‘ j)
  secId : (∀ i ∈ θ, ∀ p ∈ P ‘ i, (E ‘ ⟨i, i⟩ₖ) ‘ p = p)
  projComp : (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ p ∈ P ‘ k,
      (π ‘ ⟨i, j⟩ₖ) ‘ ((π ‘ ⟨j, k⟩ₖ) ‘ p) = (π ‘ ⟨i, k⟩ₖ) ‘ p)
  secComp : (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ p ∈ P ‘ i,
      (E ‘ ⟨j, k⟩ₖ) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (E ‘ ⟨i, k⟩ₖ) ‘ p)
  retraction : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
    (π ‘ ⟨i, j⟩ₖ) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = p)

noncomputable def forcingSectionValue (π E k p i : V) : V := by
  classical
  exact if i ∈ k then (π ‘ ⟨i, k⟩ₖ) ‘ p else (E ‘ ⟨k, i⟩ₖ) ‘ p

noncomputable def forcingSectionThread (θ π E k p : V) : V :=
  definableGraph θ (fun i ↦ forcingSectionValue π E k p i) (by
    classical
    have h : ℒₛₑₜ-relation (fun y i : V ↦
      (i ∈ k ∧ y = (π ‘ ⟨i, k⟩ₖ) ‘ p) ∨ (i ∉ k ∧ y = (E ‘ ⟨k, i⟩ₖ) ‘ p)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = forcingSectionValue π E k p (v 1) ↔ _
    by_cases hv : v 1 ∈ k <;> simp [forcingSectionValue, hv])

theorem forcingSectionThread_value {θ π E k p i : V} (hi : i ∈ θ) :
    (forcingSectionThread θ π E k p) ‘ i = forcingSectionValue π E k p i :=
  value_definableGraph _ _ _ hi

private theorem ordinal_subset_of_not_mem {i k : V} [IsOrdinal i] [IsOrdinal k]
    (h : i ∉ k) : k ⊆ i := by
  rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
  · exact (h hik).elim
  · exact fun _ hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive _ hki

theorem forcingSectionValue_mem {θ P π E k p i : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k) (hi : i ∈ θ) :
    forcingSectionValue π E k p i ∈ P ‘ i := by
  classical
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hi
  unfold forcingSectionValue
  split_ifs with hik
  · exact h.projMaps i hi k hk (IsOrdinal.toIsTransitive.transitive _ hik) p hp
  · exact h.secMaps k hk i hi (ordinal_subset_of_not_mem hik) p hp

theorem forcingSectionValue_self {θ P π E k p : V}
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k) :
    forcingSectionValue π E k p k = p := by
  classical
  simp only [forcingSectionValue, ite_eq_right (mem_irrefl k)]
  exact h.secId k hk p hp

theorem forcingSectionValue_coherent {θ P π E k p i j : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ∈ j) :
    (π ‘ ⟨i, j⟩ₖ) ‘ (forcingSectionValue π E k p j) = forcingSectionValue π E k p i := by
  classical
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hij' : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hij
  by_cases hjk : j ∈ k
  · have hik : i ∈ k := IsOrdinal.toIsTransitive.mem_trans hij hjk
    simp only [forcingSectionValue, ite_eq_left hjk, ite_eq_left hik]
    exact h.projComp i hi j hj k hk hij'
      (IsOrdinal.toIsTransitive.transitive _ hjk) p hp
  · have hkj : k ⊆ j := ordinal_subset_of_not_mem hjk
    by_cases hik : i ∈ k
    · have hik' : i ⊆ k := IsOrdinal.toIsTransitive.transitive _ hik
      simp only [forcingSectionValue, ite_eq_right hjk, ite_eq_left hik]
      rw [← h.projComp i hi k hk j hj hik' hkj _ (h.secMaps k hk j hj hkj p hp),
        h.retraction k hk j hj hkj p hp]
    · have hki : k ⊆ i := ordinal_subset_of_not_mem hik
      simp only [forcingSectionValue, ite_eq_right hjk, ite_eq_right hik]
      rw [← h.secComp k hk i hi j hj hki hij' p hp]
      exact h.retraction i hi j hj hij' _ (h.secMaps k hk i hi hki p hp)

theorem forcingSectionThread_mem {θ P π E U k p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    forcingSectionThread θ π E k p ∈ forcingDirectLimit θ P π E U := by
  classical
  have hval := fun i hi ↦ forcingSectionValue_mem h hk hp (i := i) hi
  apply (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
  constructor
  · apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ hU i hi _ (hval i hi)), ?_, ?_⟩
    · intro i hi
      rw [forcingSectionThread_value hi]
      exact hval i hi
    · intro j hj i hij hi
      rw [forcingSectionThread_value hj, forcingSectionThread_value hi]
      exact forcingSectionValue_coherent h hk hp hi hj hij
  · refine ⟨k, hk, ?_⟩
    intro j hj hkj
    have hnot : j ∉ k := fun hjk ↦ mem_irrefl j (hkj j hjk)
    rw [forcingSectionThread_value hj, forcingSectionThread_value hk,
      forcingSectionValue_self h hk hp]
    simp only [forcingSectionValue, ite_eq_right hnot]

theorem IsSplitForcingSystem.projId {θ P π E i p : V}
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hp : p ∈ P ‘ i) :
    (π ‘ ⟨i, i⟩ₖ) ‘ p = p := by
  have hr := h.retraction i hi i hi (fun _ hx ↦ hx) p hp
  rwa [h.secId i hi p hp] at hr

theorem forcingSectionThread_support {θ P π E k p : V}
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k) :
    IsThreadSupport θ E (forcingSectionThread θ π E k p) k := by
  classical
  refine ⟨hk, ?_⟩
  intro j hj hkj
  have hnot : j ∉ k := fun hjk ↦ mem_irrefl j (hkj j hjk)
  rw [forcingSectionThread_value hj, forcingSectionThread_value hk,
    forcingSectionValue_self h hk hp]
  simp only [forcingSectionValue, ite_eq_right hnot]

theorem forcingInverseLimit_project_subset {θ P π E U f i k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hf : f ∈ forcingInverseLimit θ P π U)
    (hi : i ∈ θ) (hk : k ∈ θ) (hik : i ⊆ k) :
    (π ‘ ⟨i, k⟩ₖ) ‘ (f ‘ k) = f ‘ i := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hk
  have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  rcases IsOrdinal.mem_trichotomy i k with hil | rfl | hki
  · exact hf'.2.2 k hk i hil hi
  · exact h.projId hi (hf'.2.1 i hi)
  · exact (mem_irrefl k (hik k hki)).elim

theorem forcingDirectLimit_cofinal_support {θ P π E U f i : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hf : f ∈ forcingDirectLimit θ P π E U)
    (hi : i ∈ θ) : ∃ k, IsThreadSupport θ E f k ∧ i ⊆ k := by
  obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hk.1
  rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
  · exact ⟨k, hk, IsOrdinal.toIsTransitive.transitive _ hik⟩
  · exact ⟨i, hk, fun _ hx ↦ hx⟩
  · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
    exact ⟨i, hk.raise hf'.2.1 hi hki' (fun j hj hij p hp ↦
      h.secComp k hk.1 i hi j hj hki' hij p hp), fun _ hx ↦ hx⟩

end ZFVP
