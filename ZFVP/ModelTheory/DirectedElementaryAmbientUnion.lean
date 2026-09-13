import ZFVP.ModelTheory.DirectedElementaryUnion

/-! Directed unions of submodels elementary in a common ambient membership structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsElementaryInclusion.of_common_ambient {A B C : V}
    (hAB : IsElementaryInclusion A B) (hCB : IsElementaryInclusion C B)
    (hAC : A ⊆ C) : IsElementaryInclusion A C := by
  apply IsElementaryInclusion.of_satisfaction hAB.source_nonempty hCB.source_nonempty hAC
  intro n hn φ hφ b hb
  exact (hAB.satisfaction_iff hn hφ hb).trans
    (hCB.satisfaction_iff hn hφ (mem_function_of_mem_function_of_subset hb hAC)).symm

theorem directedUnion_assignment_capture (F : V → V) (hF : ℒₛₑₜ-function₁ F) {I U : V}
    (hI : IsNonempty I)
    (hdir : ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, F i ⊆ F k ∧ F j ⊆ F k)
    (hunion : ∀ x, x ∈ U ↔ ∃ i ∈ I, x ∈ F i)
    {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ U ^ n) :
    ∃ i ∈ I, b ∈ (F i) ^ n := by
  have hcapture : ∀ n ∈ (ω : V), ∀ b : V,
      (∀ x ∈ n, b ‘ x ∈ U) → ∃ i ∈ I, ∀ x ∈ n, b ‘ x ∈ F i := by
    apply naturalNumber_induction
      (fun n ↦ ∀ b : V, (∀ x ∈ n, b ‘ x ∈ U) → ∃ i ∈ I, ∀ x ∈ n, b ‘ x ∈ F i)
      (by definability)
    · intro b _
      obtain ⟨i, hi⟩ := hI.nonempty
      exact ⟨i, hi, fun x hx ↦ False.elim (by simp [zero_def] at hx)⟩
    · intro n hn ih b hb
      obtain ⟨i, hi, hbi⟩ := ih b (fun x hx ↦ hb x (mem_succ_iff.mpr (Or.inr hx)))
      obtain ⟨j, hj, hbj⟩ := (hunion (b ‘ n)).mp (hb n (by simp))
      obtain ⟨k, hk, hik, hjk⟩ := hdir i hi j hj
      refine ⟨k, hk, fun x hx ↦ ?_⟩
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact hjk _ hbj
      · exact hik _ (hbi x hx)
  obtain ⟨i, hi, hbi⟩ := hcapture n hn b (fun x hx ↦ function_value_mem hb hx)
  let := IsFunction.of_mem hb
  refine ⟨i, hi, mem_function_iff.mpr ⟨?_, (mem_function_iff.mp hb).2⟩⟩
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hb).1 p hp)
  exact mem_prod_iff.mpr ⟨x, hx, y, (value_eq_of_kpair_mem hp) ▸ hbi x hx, rfl⟩

theorem directedUnion_elementary_ambient (F : V → V) (hF : ℒₛₑₜ-function₁ F) {I U B : V}
    (hI : IsNonempty I) (he : ∀ i ∈ I, IsElementaryInclusion (F i) B)
    (hdir : ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I, F i ⊆ F k ∧ F j ⊆ F k)
    (hunion : ∀ x, x ∈ U ↔ ∃ i ∈ I, x ∈ F i) :
    IsElementaryInclusion U B := by
  have hstages := directedUnion_elementary F hF hI (fun i hi ↦ (he i hi).source_nonempty)
    (fun i hi j hj ↦ by
      obtain ⟨k, hk, hik, hjk⟩ := hdir i hi j hj
      exact ⟨k, hk, (he i hi).of_common_ambient (he k hk) hik,
        (he j hj).of_common_ambient (he k hk) hjk⟩) hunion
  obtain ⟨i₀, hi₀⟩ := hI.nonempty
  apply IsElementaryInclusion.of_satisfaction (hstages i₀ hi₀).target_nonempty
    (he i₀ hi₀).target_nonempty
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (hunion x).mp hx
    exact (he i hi).subset x hxi
  · intro n hn φ hφ b hb
    obtain ⟨i, hi, hbi⟩ := directedUnion_assignment_capture F hF hI hdir hunion hn hb
    exact ((hstages i hi).satisfaction_iff hn hφ hbi).symm.trans
      ((he i hi).satisfaction_iff hn hφ hbi)

end ZFVP
