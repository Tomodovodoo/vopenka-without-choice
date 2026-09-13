import ZFVP.SetTheory.NaturalClosureCardinality
import ZFVP.SetTheory.InfiniteDependentChoice
import ZFVP.SetTheory.CountableSets

/-! Internal closure under operations on internally finite tuples. Both
the iteration and the tuple argument run through the model's full omega. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internallyCountable_finiteSequences (hAC : InternalChoice V) {A : V}
    (hA : IsInternallyCountable A) : IsInternallyCountable (finiteSequences A) :=
  finiteSequences_cardLE_of_cardLE_initial hAC
    ⟨IsOrdinal.ω, fun _ hn ↦ omega_not_cardLE_natural hn⟩ (subset_refl _) hA

noncomputable def finiteOperationStep (I : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) (A : V) : V :=
  A ∪ repl (fun p ↦ F (kpair.π₁ p) (kpair.π₂ p)) (by definability) (I ×ˢ finiteSequences A)

instance finiteOperationStep_definable (I : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : ℒₛₑₜ-function₁ (finiteOperationStep I F hF) := by
  unfold finiteOperationStep
  definability

theorem mem_finiteOperationStep (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A x : V) :
    x ∈ finiteOperationStep I F hF A ↔
      x ∈ A ∨ ∃ i ∈ I, ∃ s ∈ finiteSequences A, x = F i s := by
  simp only [finiteOperationStep, mem_union_iff, repl_spec, mem_prod_iff]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨p, ⟨i, hi, s, hs, rfl⟩, he⟩
    exact ⟨i, hi, s, hs, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using he⟩
  · rintro ⟨i, hi, s, hs, rfl⟩
    exact ⟨⟨i, s⟩ₖ, ⟨i, hi, s, hs, rfl⟩, by simp⟩

theorem subset_finiteOperationStep (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V) :
    A ⊆ finiteOperationStep I F hF A := fun _ hx ↦ (mem_finiteOperationStep _ _ _ _ _).mpr (Or.inl hx)

theorem finiteOperationStep_countable (hAC : InternalChoice V) {I A : V}
    (hI : IsInternallyCountable I) (hA : IsInternallyCountable A)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsInternallyCountable (finiteOperationStep I F hF A) :=
  internallyCountable_union hA (internallyCountable_repl _ _
    ((prod_cardLE_prod hI (internallyCountable_finiteSequences hAC hA)).trans omega_prod_cardLE_omega))

noncomputable def finiteOperationHull (I : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) (A : V) : V :=
  ⋃ˢ range (naturalIterationGraph (finiteOperationStep I F hF) inferInstance A)

theorem mem_finiteOperationHull (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A x : V) :
    x ∈ finiteOperationHull I F hF A ↔
      ∃ n ∈ (ω : V), x ∈ naturalIteration (finiteOperationStep I F hF) inferInstance A n := by
  simp only [finiteOperationHull, mem_sUnion_iff, mem_range_iff]
  constructor
  · rintro ⟨Y, ⟨n, hnY⟩, hx⟩
    have hn : n ∈ (ω : V) := by
      simpa only [domain_naturalIterationGraph] using mem_domain_of_kpair_mem hnY
    exact ⟨n, hn, by rw [← naturalIterationGraph_value _ _ _ hn, value_eq_of_kpair_mem hnY]; exact hx⟩
  · rintro ⟨n, hn, hx⟩
    refine ⟨naturalIteration (finiteOperationStep I F hF) inferInstance A n, ⟨n, ?_⟩, hx⟩
    rw [← naturalIterationGraph_value _ _ _ hn]
    exact kpair_value_mem (by simpa only [domain_naturalIterationGraph] using hn)

theorem subset_finiteOperationHull (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V) :
    A ⊆ finiteOperationHull I F hF A := by
  intro x hx
  exact (mem_finiteOperationHull _ _ _ _ _).mpr ⟨0, by simp, by simpa only [naturalIteration_zero] using hx⟩

theorem finiteOperationHull_countable (hAC : InternalChoice V) {I A : V}
    (hI : IsInternallyCountable I) (hA : IsInternallyCountable A)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsInternallyCountable (finiteOperationHull I F hF A) :=
  naturalIteration_union_cardLE hAC
    ⟨IsOrdinal.ω, fun _ hn ↦ omega_not_cardLE_natural hn⟩ (subset_refl _)
    (finiteOperationStep I F hF) inferInstance hA
    (fun _ hX ↦ finiteOperationStep_countable hAC hI hX F hF)

theorem finiteOperationStage_mono (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V)
    {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) :
    naturalIteration (finiteOperationStep I F hF) inferInstance A n ⊆
      naturalIteration (finiteOperationStep I F hF) inferInstance A m := by
  let : IsOrdinal n := IsOrdinal.of_mem hn
  let : IsOrdinal m := IsOrdinal.of_mem hm
  rcases IsOrdinal.subset_iff.mp hnm with rfl | hnm
  · exact subset_refl _
  · apply natural_increasing_subset _ (by definability) ?_ m hm n hnm
    intro k hk
    rw [naturalIteration_succ _ _ _ hk]
    exact subset_finiteOperationStep _ _ _ _

theorem finiteOperationStage_common (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V)
    {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) :
    ∃ k ∈ (ω : V),
      naturalIteration (finiteOperationStep I F hF) inferInstance A n ⊆
        naturalIteration (finiteOperationStep I F hF) inferInstance A k ∧
      naturalIteration (finiteOperationStep I F hF) inferInstance A m ⊆
        naturalIteration (finiteOperationStep I F hF) inferInstance A k := by
  let : IsOrdinal n := IsOrdinal.of_mem hn
  let : IsOrdinal m := IsOrdinal.of_mem hm
  rcases IsOrdinal.subset_or_supset n m with h | h
  · exact ⟨m, hm, finiteOperationStage_mono _ _ _ _ hn hm h, subset_refl _⟩
  · exact ⟨n, hn, subset_refl _, finiteOperationStage_mono _ _ _ _ hm hn h⟩

/-- Every internally finite tuple in the hull already lies in one stage.
The proof uses internal finite-sequence induction, including nonstandard lengths. -/
theorem finiteOperationHull_tuple_stage (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V)
    {s : V} (hs : s ∈ finiteSequences (finiteOperationHull I F hF A)) :
    ∃ n ∈ (ω : V), s ∈ finiteSequences (naturalIteration (finiteOperationStep I F hF) inferInstance A n) := by
  let C := naturalIteration (finiteOperationStep I F hF) inferInstance A
  have h (s : V) (hs : s ∈ finiteSequences (finiteOperationHull I F hF A)) :
      ∃ n ∈ (ω : V), range s ⊆ C n := by
    apply finiteSequence_induction _ (fun t ↦ ∃ n ∈ (ω : V), range t ⊆ C n) (by definability) ?_ ?_ s hs
    · exact ⟨0, by simp, by simp only [range_empty]; exact empty_subset _⟩
    · intro k _ t _ x hx ht
      obtain ⟨n, hn, ht⟩ := ht
      obtain ⟨m, hm, hx⟩ := (mem_finiteOperationHull _ _ _ _ _).mp hx
      obtain ⟨l, hl, hnl, hml⟩ := finiteOperationStage_common I F hF A hn hm
      refine ⟨l, hl, ?_⟩
      rw [range_insert]
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact hml _ hx
      · exact hnl y (ht y hy)
  obtain ⟨n, hn, hr⟩ := h s hs
  obtain ⟨k, hk, hsk⟩ := (mem_finiteSequences_iff _ _).mp hs
  let : IsFunction s := IsFunction.of_mem hsk
  refine ⟨n, hn, (mem_finiteSequences_iff _ _).mpr ⟨k, hk, ?_⟩⟩
  have hf := mem_function_of_mem_function_of_subset (IsFunction.mem_function s) hr
  simpa only [domain_eq_of_mem_function hsk] using hf

theorem finiteOperationHull_closed (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (A : V)
    {i s : V} (hi : i ∈ I) (hs : s ∈ finiteSequences (finiteOperationHull I F hF A)) :
    F i s ∈ finiteOperationHull I F hF A := by
  obtain ⟨n, hn, hs⟩ := finiteOperationHull_tuple_stage I F hF A hs
  apply (mem_finiteOperationHull _ _ _ _ _).mpr
  refine ⟨succ n, ω_succ_closed hn, ?_⟩
  rw [naturalIteration_succ _ _ _ hn, mem_finiteOperationStep]
  exact Or.inr ⟨i, hi, s, hs, rfl⟩

theorem finiteOperationHull_subset (I : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    {A D : V} (hA : A ⊆ D)
    (hclosed : ∀ i ∈ I, ∀ s ∈ finiteSequences D, F i s ∈ D) :
    finiteOperationHull I F hF A ⊆ D := by
  have hstage := naturalIteration_invariant (finiteOperationStep I F hF) inferInstance A
    (fun X ↦ X ⊆ D) (by definability) hA (by
      intro X hX x hx
      rcases (mem_finiteOperationStep _ _ _ _ _).mp hx with hx | ⟨i, hi, s, hs, rfl⟩
      · exact hX x hx
      · apply hclosed i hi s
        obtain ⟨n, hn, hs⟩ := (mem_finiteSequences_iff _ _).mp hs
        exact (mem_finiteSequences_iff _ _).mpr ⟨n, hn, mem_function_of_mem_function_of_subset hs hX⟩)
  intro x hx
  obtain ⟨n, hn, hx⟩ := (mem_finiteOperationHull _ _ _ _ _).mp hx
  exact hstage n hn x hx

end ZFVP.Schmerl
