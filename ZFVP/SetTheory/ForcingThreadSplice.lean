import ZFVP.SetTheory.ForcingSectionThread

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Coded stronger lifts whose projections agree with the earlier lift operations. -/
structure IsCoherentForcingLift (θ P R π L : V) : Prop where
  lift : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ P ‘ j, ∀ b ∈ P ‘ i,
    ⟨b, (π ‘ ⟨i, j⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
    (L ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ ∈ P ‘ j ∧
    ⟨(L ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ, a⟩ₖ ∈ R ‘ j ∧
    (π ‘ ⟨i, j⟩ₖ) ‘ ((L ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) = b)
  commute : (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ i, ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
    (π ‘ ⟨j, k⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ) =
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(π ‘ ⟨j, k⟩ₖ) ‘ a, b⟩ₖ)

noncomputable def forcingSpliceValue (π L f i b j : V) : V := by
  classical
  exact if j ∈ i then (π ‘ ⟨j, i⟩ₖ) ‘ b else (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ

noncomputable def forcingThreadSplice (θ π L f i b : V) : V :=
  definableGraph θ (fun j ↦ forcingSpliceValue π L f i b j) (by
    classical
    have h : ℒₛₑₜ-relation (fun y j : V ↦
      (j ∈ i ∧ y = (π ‘ ⟨j, i⟩ₖ) ‘ b) ∨
      (j ∉ i ∧ y = (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = forcingSpliceValue π L f i b (v 1) ↔ _
    by_cases hv : v 1 ∈ i <;> simp [forcingSpliceValue, hv])

theorem forcingThreadSplice_value {θ π L f i b j : V} (hj : j ∈ θ) :
    (forcingThreadSplice θ π L f i b) ‘ j = forcingSpliceValue π L f i b j :=
  value_definableGraph _ _ _ hj

private theorem subset_of_not_mem {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hji : j ∉ i) : i ⊆ j := by
  rcases IsOrdinal.mem_trichotomy j i with hj | rfl | hi
  · exact (hji hj).elim
  · exact fun _ hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive _ hi

theorem forcingSpliceValue_lift {θ P R π E L U f i b j : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hj : j ∈ θ) (hij : i ⊆ j) :
    forcingSpliceValue π L f i b j ∈ P ‘ j ∧
    ⟨forcingSpliceValue π L f i b j, f ‘ j⟩ₖ ∈ R ‘ j ∧
    (π ‘ ⟨i, j⟩ₖ) ‘ (forcingSpliceValue π L f i b j) = b := by
  classical
  have hnot : j ∉ i := fun hji ↦ mem_irrefl j (hij j hji)
  simp only [forcingSpliceValue, ite_eq_right hnot]
  apply hL.lift i hi j hj hij _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 j hj) b hb
  rwa [forcingInverseLimit_project_subset h hf hi hj hij]

theorem forcingSpliceValue_self {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) : forcingSpliceValue π L f i b i = b := by
  have hl := forcingSpliceValue_lift h hL hf hi hb hle hi (fun _ hx ↦ hx)
  exact (h.projId hi hl.1).symm.trans hl.2.2

theorem forcingSpliceValue_mem {θ P R π E L U f i b j : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hj : j ∈ θ) :
    forcingSpliceValue π L f i b j ∈ P ‘ j := by
  classical
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  by_cases hji : j ∈ i
  · simp only [forcingSpliceValue, ite_eq_left hji]
    exact h.projMaps j hj i hi (IsOrdinal.toIsTransitive.transitive _ hji) b hb
  · exact (forcingSpliceValue_lift h hL hf hi hb hle hj (subset_of_not_mem hji)).1

theorem forcingSpliceValue_coherent {θ P R π E L U f i b j k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hj : j ∈ θ) (hk : k ∈ θ) (hjk : j ∈ k) :
    (π ‘ ⟨j, k⟩ₖ) ‘ (forcingSpliceValue π L f i b k) = forcingSpliceValue π L f i b j := by
  classical
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  have hjk' : j ⊆ k := IsOrdinal.toIsTransitive.transitive _ hjk
  by_cases hki : k ∈ i
  · have hji : j ∈ i := IsOrdinal.toIsTransitive.mem_trans hjk hki
    simp only [forcingSpliceValue, ite_eq_left hki, ite_eq_left hji]
    exact h.projComp j hj k hk i hi hjk' (IsOrdinal.toIsTransitive.transitive _ hki) b hb
  · have hik : i ⊆ k := subset_of_not_mem hki
    have hklift := forcingSpliceValue_lift h hL hf hi hb hle hk hik
    by_cases hji : j ∈ i
    · have hji' : j ⊆ i := IsOrdinal.toIsTransitive.transitive _ hji
      rw [← h.projComp j hj i hi k hk hji' hik _ hklift.1, hklift.2.2]
      simp only [forcingSpliceValue, ite_eq_left hji]
    · have hij : i ⊆ j := subset_of_not_mem hji
      simp only [forcingSpliceValue, ite_eq_right hki, ite_eq_right hji]
      have hbound : ⟨b, (π ‘ ⟨i, k⟩ₖ) ‘ (f ‘ k)⟩ₖ ∈ R ‘ i := by
        rwa [forcingInverseLimit_project_subset h hf hi hk hik]
      rw [hL.commute i hi j hj k hk hij hjk' _
        (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk) b hb hbound,
        forcingInverseLimit_project_subset h hf hj hk hjk']

theorem forcingThreadSplice_mem {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U) :
    forcingThreadSplice θ π L f i b ∈ forcingInverseLimit θ P π U := by
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun j hj ↦
    hU j hj _ (forcingSpliceValue_mem h hL hf hi hb hle hj)), ?_, ?_⟩
  · intro j hj
    rw [forcingThreadSplice_value hj]
    exact forcingSpliceValue_mem h hL hf hi hb hle hj
  · intro k hk j hjk hj
    rw [forcingThreadSplice_value hk, forcingThreadSplice_value hj]
    exact forcingSpliceValue_coherent h hL hf hi hb hle hj hk hjk

theorem forcingThreadSplice_le {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hπ : ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j) :
    ⟨forcingThreadSplice θ π L f i b, f⟩ₖ ∈
      forcingThreadOrder θ R (forcingInverseLimit θ P π U) := by
  classical
  have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  let := IsOrdinal.of_mem hi
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨forcingThreadSplice_mem h hL hf hi hb hle hU, hf, ?_⟩
  intro j hj
  let := IsOrdinal.of_mem hj
  rw [forcingThreadSplice_value hj]
  by_cases hji : j ∈ i
  · rw [← hf'.2.2 i hi j hji hj]
    simpa only [forcingSpliceValue, ite_eq_left hji] using hπ j hji b hb _ (hf'.2.1 i hi) hle
  · exact (forcingSpliceValue_lift h hL hf hi hb hle hj (subset_of_not_mem hji)).2.1

end ZFVP
