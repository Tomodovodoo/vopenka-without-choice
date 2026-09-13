import ZFVP.SetTheory.BaireRunBlocks

/-! Uniform internal recursion for the finite prefixes of the run encoding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def baireRunStepFormula : SetTheorySemisentence 3 :=
  f“z s x. z = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn x))
    (!binaryAppendRunFormula (!kpair.π₂.dfn x) (!value.dfn s (!kpair.π₁.dfn x)))”

def baireRunStateStepFormula : SetTheorySemisentence 3 :=
  f“z s g. (!domain.dfn g = !isEmpty ∧ z = !kpair.dfn (!isEmpty) (!isEmpty)) ∨
    (!domain.dfn g ≠ !isEmpty ∧
      !baireRunStepFormula z s (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def baireRunStateFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula baireRunStateStepFormula

def baireRunPrefixFormula : SetTheorySemisentence 3 :=
  f“p s n. p = !kpair.π₂.dfn (!baireRunStateFormula s n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def baireRunStep (s x : V) : V :=
  ⟨succ (kpair.π₁ x), binaryAppendRun (kpair.π₂ x) (s ‘ (kpair.π₁ x))⟩ₖ

instance baireRunStepFormula_defined :
    ℒₛₑₜ-function₂[V] baireRunStep via baireRunStepFormula :=
  ⟨fun v ↦ by simp [baireRunStepFormula, baireRunStep]⟩

instance baireRunStep_definable : ℒₛₑₜ-function₂[V] baireRunStep :=
  baireRunStepFormula_defined.to_definable

noncomputable def baireRunStateStep (s g : V) : V :=
  naturalIterationStep (baireRunStep s) ⟨0, ∅⟩ₖ g

instance baireRunStateStepFormula_defined :
    ℒₛₑₜ-function₂[V] baireRunStateStep via baireRunStateStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [baireRunStateStepFormula, baireRunStateStep, naturalIterationStep, zero_def]
    · simp_all [baireRunStateStepFormula, baireRunStateStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance baireRunStateStep_definable : ℒₛₑₜ-function₂[V] baireRunStateStep :=
  baireRunStateStepFormula_defined.to_definable

noncomputable def baireRunState (s n : V) : V :=
  naturalIteration (baireRunStep s) (by definability) ⟨0, ∅⟩ₖ n

instance baireRunStateFormula_defined :
    ℒₛₑₜ-function₂[V] baireRunState via baireRunStateFormula :=
  parameterRecursionFormula_defined baireRunStateStep baireRunStateStepFormula

instance baireRunState_definable : ℒₛₑₜ-function₂[V] baireRunState :=
  baireRunStateFormula_defined.to_definable

noncomputable def baireRunPrefix (s n : V) : V := kpair.π₂ (baireRunState s n)

instance baireRunPrefixFormula_defined :
    ℒₛₑₜ-function₂[V] baireRunPrefix via baireRunPrefixFormula :=
  ⟨fun v ↦ by simp [baireRunPrefixFormula, baireRunPrefix]⟩

instance baireRunPrefix_definable : ℒₛₑₜ-function₂[V] baireRunPrefix :=
  baireRunPrefixFormula_defined.to_definable

theorem baireRunState_index (s : V) {n : V} (hn : n ∈ (ω : V)) :
    kpair.π₁ (baireRunState s n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (baireRunState s n) = n) (by definability) ?_ ?_ n hn
  · simp [baireRunState, naturalIteration_zero]
  · intro n hn ih
    simp only [baireRunState, naturalIteration_succ _ _ _ hn, baireRunStep, kpair.π₁_kpair]
    exact congrArg succ ih

theorem baireRunPrefix_zero (s : V) : baireRunPrefix s 0 = ∅ := by
  simp [baireRunPrefix, baireRunState, naturalIteration_zero]

theorem baireRunPrefix_succ (s : V) {n : V} (hn : n ∈ (ω : V)) :
    baireRunPrefix s (succ n) = binaryAppendRun (baireRunPrefix s n) (s ‘ n) := by
  change kpair.π₂ (naturalIteration (baireRunStep s) _ ⟨0, ∅⟩ₖ (succ n)) = _
  rw [naturalIteration_succ _ _ _ hn]
  simp only [baireRunStep, kpair.π₂_kpair]
  change binaryAppendRun (baireRunPrefix s n) (s ‘ (kpair.π₁ (baireRunState s n))) = _
  rw [baireRunState_index s hn]

theorem baireRunPrefix_mem {s m n : V} (hs : s ∈ (ω : V) ^ m)
    (hn : n ∈ (ω : V)) (hnm : n ⊆ m) : baireRunPrefix s n ∈ binarySequences V := by
  apply naturalNumber_induction (fun n ↦ n ⊆ m → baireRunPrefix s n ∈ binarySequences V)
    (by definability) ?_ ?_ n hn hnm
  · intro _
    rw [baireRunPrefix_zero]
    exact empty_mem_finiteSequences _
  · intro n hn ih hsub
    rw [baireRunPrefix_succ s hn]
    exact binaryAppendRun_mem (ih (subset_trans (mem_subset_refl n) hsub))
      (function_value_mem hs (hsub n (mem_succ_self n)))

theorem baireRunPrefix_agree {s t n : V} (hn : n ∈ (ω : V))
    (h : ∀ i ∈ n, s ‘ i = t ‘ i) : baireRunPrefix s n = baireRunPrefix t n := by
  apply naturalNumber_induction
    (fun n ↦ (∀ i ∈ n, s ‘ i = t ‘ i) → baireRunPrefix s n = baireRunPrefix t n)
    (by definability) ?_ ?_ n hn h
  · intro _
    rw [baireRunPrefix_zero, baireRunPrefix_zero]
  · intro n hn ih hst
    rw [baireRunPrefix_succ s hn, baireRunPrefix_succ t hn,
      ih (fun i hi ↦ hst i (mem_succ_iff.mpr (Or.inr hi))), hst n (mem_succ_self n)]

theorem baireRunPrefix_restrict {s n : V} [IsFunction s] (hn : n ∈ (ω : V))
    (hnm : n ⊆ domain s) : baireRunPrefix (s ↾ n) n = baireRunPrefix s n :=
  baireRunPrefix_agree hn (fun i hi ↦ value_restrict (hnm i hi) hi)

theorem baireRunPrefix_extends {s m n : V} [IsOrdinal m] (hs : s ∈ (ω : V) ^ m)
    (hn : n ∈ (ω : V)) (hnm : n ∈ m) :
    baireRunPrefix s n ⊆ baireRunPrefix s (succ n) := by
  rw [baireRunPrefix_succ s hn]
  have hsub : n ⊆ m := IsOrdinal.toIsTransitive.transitive n hnm
  exact binaryAppendRun_extends (baireRunPrefix_mem hs hn hsub) (function_value_mem hs hnm)

theorem baireRunPrefix_mono {s m n k : V} [IsOrdinal m] (hs : s ∈ (ω : V) ^ m)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (hnk : n ⊆ k) (hkm : k ⊆ m) :
    baireRunPrefix s n ⊆ baireRunPrefix s k := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  apply naturalNumber_induction
    (fun k ↦ k ⊆ m → ∀ n ∈ (ω : V), n ⊆ k → baireRunPrefix s n ⊆ baireRunPrefix s k)
    (by definability) ?_ ?_ k hk hkm n hn hnk
  · intro _ n hn hn0
    have he : n = 0 := subset_empty_iff_eq_empty.mp hn0
    rw [he]
  · intro k hk ih hkm n hn hnk
    have : IsOrdinal k := IsOrdinal.of_mem hk
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rcases IsOrdinal.subset_iff.mp hnk with rfl | hnks
    · exact subset_refl _
    · have hnk' : n ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hnks)
      exact subset_trans (ih (subset_trans (mem_subset_refl k) hkm) n hn hnk')
        (baireRunPrefix_extends hs hk (hkm k (mem_succ_self k)))

theorem baireRunPrefix_length_bound {s m n : V} (hs : s ∈ (ω : V) ^ m)
    (hn : n ∈ (ω : V)) (hnm : n ⊆ m) : n ⊆ domain (baireRunPrefix s n) := by
  apply naturalNumber_induction (fun n ↦ n ⊆ m → n ⊆ domain (baireRunPrefix s n))
    (by definability) ?_ ?_ n hn hnm
  · intro _
    exact empty_subset _
  · intro n hn ih hnm
    have hnm' := subset_trans (mem_subset_refl n) hnm
    have hp := baireRunPrefix_mem hs hn hnm'
    obtain ⟨hpω, hpf⟩ := (mem_finiteSequences_iff_domain _ _).mp hp
    have ha := function_value_mem hs (hnm n (mem_succ_self n))
    have := IsOrdinal.of_mem ha
    rw [baireRunPrefix_succ s hn, binaryAppendRun_domain hpf]
    have hsub := subset_trans (ih hnm') (subset_ordinalAdd (domain (baireRunPrefix s n)) (s ‘ n))
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal (domain (baireRunPrefix s n)) := IsOrdinal.of_mem hpω
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hsub)
    · exact mem_succ_iff.mpr (Or.inr (hsub i hi))

noncomputable def baireFiniteRunCode (s : V) : V := baireRunPrefix s (domain s)

instance baireFiniteRunCode_definable : ℒₛₑₜ-function₁[V] baireFiniteRunCode := by
  unfold baireFiniteRunCode
  definability

theorem baireFiniteRunCode_mem {s : V} (hs : s ∈ naturalSequences V) :
    baireFiniteRunCode s ∈ binarySequences V := by
  obtain ⟨hn, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  exact baireRunPrefix_mem hsf hn (subset_refl _)

end ZFVP
