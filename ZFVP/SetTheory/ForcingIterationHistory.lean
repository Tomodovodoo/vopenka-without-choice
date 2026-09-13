import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingHistoryTable (θ H : V) (c : V → V)
    (hc : ℒₛₑₜ-function₁ c) : V :=
  iterationTableUnion θ (fun i ↦ c (H ‘ i)) (by definability)

noncomputable def forcingIterationCodeUnion (θ H : V) : V :=
  forcingIterationCode
    (forcingHistoryTable θ H forcingCodeP forcingCodeP_definable)
    (forcingHistoryTable θ H forcingCodeR forcingCodeR_definable)
    (forcingHistoryTable θ H forcingCodeπ forcingCodeπ_definable)
    (forcingHistoryTable θ H forcingCodeE forcingCodeE_definable)
    (forcingHistoryTable θ H forcingCodeL forcingCodeL_definable)
    (forcingHistoryTable θ H forcingCodet forcingCodet_definable)

structure IsForcingIterationHistory (θ H : V) : Prop where
  table : IsIterationTable θ H
  stage : (∀ i ∈ θ, IsForcingIterationCode (succ i) (H ‘ i))
  increasing : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ForcingCodeExtends (H ‘ i) (H ‘ j))

theorem IsForcingIterationHistory.directed {θ H : V} [IsOrdinal θ]
    (h : IsForcingIterationHistory θ H) {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) :
    ∃ k ∈ θ, ForcingCodeExtends (H ‘ i) (H ‘ k) ∧ ForcingCodeExtends (H ‘ j) (H ‘ k) := by
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · exact ⟨j, hj, h.increasing i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij),
      ForcingCodeExtends.refl _⟩
  · exact ⟨i, hi, ForcingCodeExtends.refl _, ForcingCodeExtends.refl _⟩
  · exact ⟨i, hi, ForcingCodeExtends.refl _,
      h.increasing j hj i hi (IsOrdinal.toIsTransitive.transitive _ hji)⟩

theorem IsForcingIterationHistory.union_code {θ H : V} [IsOrdinal θ]
    (h : IsForcingIterationHistory θ H) :
    IsForcingIterationCode θ (forcingIterationCodeUnion θ H) := by
  have cP : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodeP (H ‘ i) ⊆ forcingCodeP (H ‘ k) ∧
      forcingCodeP (H ‘ j) ⊆ forcingCodeP (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subP, hjk.subP⟩
  have cR : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodeR (H ‘ i) ⊆ forcingCodeR (H ‘ k) ∧
      forcingCodeR (H ‘ j) ⊆ forcingCodeR (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subR, hjk.subR⟩
  have cπ : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodeπ (H ‘ i) ⊆ forcingCodeπ (H ‘ k) ∧
      forcingCodeπ (H ‘ j) ⊆ forcingCodeπ (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subπ, hjk.subπ⟩
  have cE : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodeE (H ‘ i) ⊆ forcingCodeE (H ‘ k) ∧
      forcingCodeE (H ‘ j) ⊆ forcingCodeE (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subE, hjk.subE⟩
  have cL : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodeL (H ‘ i) ⊆ forcingCodeL (H ‘ k) ∧
      forcingCodeL (H ‘ j) ⊆ forcingCodeL (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subL, hjk.subL⟩
  have ct : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ,
      forcingCodet (H ‘ i) ⊆ forcingCodet (H ‘ k) ∧
      forcingCodet (H ‘ j) ⊆ forcingCodet (H ‘ k) := by
    intro i hi j hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed hi hj
    exact ⟨k, hk, hik.subt, hjk.subt⟩
  unfold forcingIterationCodeUnion
  constructor
  · simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
      forcingCodeE_code, forcingCodeL_code, forcingCodet_code]
    exact forcingIterationSystem_union (by definability) (by definability)
      (by definability) (by definability) (by definability) (by definability)
      (fun i hi ↦ (h.stage i hi).tableP) (fun i hi ↦ (h.stage i hi).tableR) (fun i hi ↦ (h.stage i hi).tableπ) (fun i hi ↦ (h.stage i hi).tableE) (fun i hi ↦ (h.stage i hi).tableL) (fun i hi ↦ (h.stage i hi).tablet)
      cP cR cπ cE cL ct (fun i hi ↦ (h.stage i hi).system)
  · simp only [forcingCodeP_code]
    exact iterationTableUnion_family (by definability) (fun i hi ↦ (h.stage i hi).tableP) cP
  · simp only [forcingCodeR_code]
    exact iterationTableUnion_family (by definability) (fun i hi ↦ (h.stage i hi).tableR) cR
  · simp only [forcingCodeπ_code]
    exact iterationTableUnion_matrix (by definability) (fun i hi ↦ (h.stage i hi).tableπ) cπ
  · simp only [forcingCodeE_code]
    exact iterationTableUnion_matrix (by definability) (fun i hi ↦ (h.stage i hi).tableE) cE
  · simp only [forcingCodeL_code]
    exact iterationTableUnion_matrix (by definability) (fun i hi ↦ (h.stage i hi).tableL) cL
  · simp only [forcingCodet_code]
    exact iterationTableUnion_family (by definability) (fun i hi ↦ (h.stage i hi).tablet) ct

theorem forcingHistoryTable_extends {θ H i : V} (hi : i ∈ θ)
    (c : V → V) (hc : ℒₛₑₜ-function₁ c) : c (H ‘ i) ⊆ forcingHistoryTable θ H c hc := by
  intro p hp
  exact mem_sUnion_iff.mpr ⟨c (H ‘ i), (repl_spec (by definability)).mpr ⟨i, hi, rfl⟩, hp⟩

theorem forcingIterationCodeUnion_extends {θ H i : V} (hi : i ∈ θ) :
    ForcingCodeExtends (H ‘ i) (forcingIterationCodeUnion θ H) := by
  unfold forcingIterationCodeUnion
  constructor
  · simpa only [forcingCodeP_code] using forcingHistoryTable_extends hi forcingCodeP forcingCodeP_definable
  · simpa only [forcingCodeR_code] using forcingHistoryTable_extends hi forcingCodeR forcingCodeR_definable
  · simpa only [forcingCodeπ_code] using forcingHistoryTable_extends hi forcingCodeπ forcingCodeπ_definable
  · simpa only [forcingCodeE_code] using forcingHistoryTable_extends hi forcingCodeE forcingCodeE_definable
  · simpa only [forcingCodeL_code] using forcingHistoryTable_extends hi forcingCodeL forcingCodeL_definable
  · simpa only [forcingCodet_code] using forcingHistoryTable_extends hi forcingCodet forcingCodet_definable

end ZFVP
