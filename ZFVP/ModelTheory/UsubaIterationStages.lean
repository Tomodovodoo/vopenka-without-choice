import ZFVP.ModelTheory.UsubaIterationRecursion
import ZFVP.SetTheory.ClassForcingCodePrefixes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)
local notation "C" => usubaCodeSequence (V := V)

noncomputable def usubaIterationPrefix (θ : V) : V := (C).codePrefix θ

instance usubaIterationPrefix_definable : ℒₛₑₜ-function₁[V] usubaIterationPrefix := (C).prefix_definable

instance usubaIterationRec_definable : ℒₛₑₜ-function₁[V] usubaIterationRec := (C).definable

theorem usubaIterationPrefix_valid (θ : V) [IsOrdinal θ] :
    IsForcingIterationCode θ (usubaIterationPrefix θ) := (C).prefix_valid θ

theorem usubaIterationPrefix_P {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodeP (usubaIterationPrefix θ)) ‘ i = (T).P i := (C).prefix_P hi

theorem usubaIterationPrefix_R {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodeR (usubaIterationPrefix θ)) ‘ i = (T).R i := (C).prefix_R hi

theorem usubaIterationPrefix_top {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    (forcingCodet (usubaIterationPrefix θ)) ‘ i = (T).top i := (C).prefix_top hi

theorem usubaIterationPrefix_projection {θ i j : V} [IsOrdinal θ] [IsOrdinal i]
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeπ (usubaIterationPrefix θ)) ‘ ⟨i, j⟩ₖ = (T).projection i j :=
  (C).prefix_projection hj hij

theorem usubaIterationPrefix_section {θ i j : V} [IsOrdinal θ] [IsOrdinal i]
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeE (usubaIterationPrefix θ)) ‘ ⟨i, j⟩ₖ = (T).sectionMap i j :=
  (C).prefix_section hj hij

theorem usubaIterationRec_stageRule (θ : V) [IsOrdinal θ] :
    usubaIterationRec θ = usubaStageRule θ (usubaIterationPrefix θ) := usubaIterationRec_rule θ

theorem usubaIterationRec_zero : usubaIterationRec (∅ : V) = usubaInitialCode := by
  rw [usubaIterationRec_stageRule, usubaStageRule_initial]

theorem usubaIterationRec_succ (k : V) [IsOrdinal k] :
    usubaIterationRec (succ k) = usubaIterationSuccessor k (usubaIterationPrefix (succ k)) := by
  rw [usubaIterationRec_stageRule, usubaStageRule_successor]

theorem usubaIterationRec_limit {θ : V} [IsOrdinal θ]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) :
    usubaIterationRec θ = forcingInverseCode θ (usubaIterationPrefix θ) := by
  rw [usubaIterationRec_stageRule]
  simp only [usubaStageRule, ite_eq_right hz, ite_eq_right hs]

theorem usubaTower_P_zero : (T).P ∅ = {∅} := by
  change (forcingCodeP (usubaIterationRec ∅)) ‘ ∅ = _
  rw [usubaIterationRec_zero]
  simp [usubaInitialCode, forcingInitialCode, forcingFamilyNext_new]

theorem usubaTower_R_zero : (T).R ∅ = reverseInclusionOrder {∅} := by
  change (forcingCodeR (usubaIterationRec ∅)) ‘ ∅ = _
  rw [usubaIterationRec_zero]
  simp [usubaInitialCode, forcingInitialCode, forcingFamilyNext_new]

theorem usubaTower_top_zero : (T).top ∅ = ∅ := by
  change (forcingCodet (usubaIterationRec ∅)) ‘ ∅ = _
  rw [usubaIterationRec_zero]
  simp [usubaInitialCode, forcingInitialCode, forcingFamilyNext_new]

theorem usubaTower_P_succ (k : V) [IsOrdinal k] :
    (T).P (succ k) = twoStepConditions ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅ := by
  change (forcingCodeP (usubaIterationRec (succ k))) ‘ (succ k) = _
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode_poset,
    usubaIterationPrefix_P (mem_succ_self k), usubaIterationPrefix_R (mem_succ_self k)]

theorem usubaTower_R_succ (k : V) [IsOrdinal k] :
    (T).R (succ k) = twoStepOrder ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k))
      (reverseInclusionOrderName ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k))) ∅ := by
  change (forcingCodeR (usubaIterationRec (succ k))) ‘ (succ k) = _
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode_order,
    usubaIterationPrefix_P (mem_succ_self k), usubaIterationPrefix_R (mem_succ_self k)]

theorem usubaTower_top_succ (k : V) [IsOrdinal k] : (T).top (succ k) = ⟨(T).top k, ∅⟩ₖ := by
  change (forcingCodet (usubaIterationRec (succ k))) ‘ (succ k) = _
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode_top, usubaIterationPrefix_top (mem_succ_self k)]

theorem usubaTower_projection_first {k c : V} [IsOrdinal k] (hc : c ∈ (T).P (succ k)) :
    ((T).projection k (succ k)) ‘ c = kpair.π₁ c := by
  have hc' := hc
  rw [usubaTower_P_succ k] at hc'
  have hfirst := function_value_mem (twoStepProjection_maps _ _ _ _) hc'
  rw [twoStepProjection_value hc'] at hfirst
  change ((forcingCodeπ (usubaIterationRec (succ k))) ‘ ⟨k, succ k⟩ₖ) ‘ c = _
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column (mem_succ_self k),
    usubaIterationPrefix_P (mem_succ_self k), usubaIterationPrefix_R (mem_succ_self k),
    successorProjectionColumn_value (mem_succ_self k) hc',
    usubaIterationPrefix_projection (mem_succ_self k) (subset_refl k)]
  exact (T).projection_self k inferInstance _ hfirst

theorem usubaTower_projection_succ {i k c : V} [IsOrdinal i] [IsOrdinal k]
    (hik : i ⊆ k) (hc : c ∈ (T).P (succ k)) :
    ((T).projection i (succ k)) ‘ c = ((T).projection i k) ‘ (kpair.π₁ c) := by
  rw [← usubaTower_projection_first hc]
  exact ((T).projection_comp i k (succ k) inferInstance inferInstance inferInstance hik
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) c hc).symm

theorem usubaTower_P_limit {θ : V} [IsOrdinal θ]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) :
    (T).P θ = forcingInverseLimit θ (forcingCodeP (usubaIterationPrefix θ))
      (forcingCodeπ (usubaIterationPrefix θ)) (forcingCodeUniverse (usubaIterationPrefix θ)) := by
  change (forcingCodeP (usubaIterationRec θ)) ‘ θ = _
  rw [usubaIterationRec_limit hz hs]
  simp only [forcingInverseCode, forcingThreadCode_poset]

theorem usubaTower_R_limit {θ : V} [IsOrdinal θ]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) :
    (T).R θ = forcingThreadOrder θ (forcingCodeR (usubaIterationPrefix θ)) ((T).P θ) := by
  change (forcingCodeR (usubaIterationRec θ)) ‘ θ = _
  rw [usubaIterationRec_limit hz hs]
  simp only [forcingInverseCode, forcingThreadCode_order, usubaTower_P_limit hz hs]

theorem usubaTower_projection_limit {θ i c : V} [IsOrdinal θ] [IsOrdinal i]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) (hi : i ∈ θ) (hc : c ∈ (T).P θ) :
    ((T).projection i θ) ‘ c = c ‘ i := by
  have hc' := hc
  rw [usubaTower_P_limit hz hs] at hc'
  change ((forcingCodeπ (usubaIterationRec θ)) ‘ ⟨i, θ⟩ₖ) ‘ c = _
  rw [usubaIterationRec_limit hz hs]
  simp only [forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi,
    forcingThreadCoordinate_value hc']

theorem usubaTower_inverse_coordinate {θ i c : V} [IsOrdinal θ]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) (hi : i ∈ θ) (hc : c ∈ (T).P θ) :
    c ‘ i ∈ (T).P i := by
  rw [usubaTower_P_limit hz hs] at hc
  have h := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 i hi
  rwa [usubaIterationPrefix_P hi] at h

theorem usubaTower_inverse_project {θ i j c : V} [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) (hi : i ∈ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) (hc : c ∈ (T).P θ) : ((T).projection i j) ‘ (c ‘ j) = c ‘ i := by
  rw [← usubaTower_projection_limit hz hs hi hc, ← usubaTower_projection_limit hz hs hj hc]
  exact (T).projection_comp i j θ inferInstance inferInstance inferInstance hij
    (IsOrdinal.toIsTransitive.transitive _ hj) c hc

theorem usubaTower_inverse_successor_first {θ k c : V} [IsOrdinal θ] [IsOrdinal k]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ)) (hk : succ k ∈ θ) (hc : c ∈ (T).P θ) :
    kpair.π₁ (c ‘ (succ k)) = c ‘ k := by
  rw [← usubaTower_projection_first (usubaTower_inverse_coordinate hz hs hk hc)]
  exact usubaTower_inverse_project hz hs (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk)
    hk (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) hc

theorem usubaTower_section_succ {i k p : V} [IsOrdinal i] [IsOrdinal k]
    (hik : i ⊆ k) (hp : p ∈ (T).P i) :
    ((T).sectionMap i (succ k)) ‘ p = ⟨((T).sectionMap i k) ‘ p, ∅⟩ₖ := by
  have hi : i ∈ succ k := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hik)
  have hp' : p ∈ (forcingCodeP (usubaIterationPrefix (succ k))) ‘ i := by
    rw [usubaIterationPrefix_P hi]
    exact hp
  change ((forcingCodeE (usubaIterationRec (succ k))) ‘ ⟨i, succ k⟩ₖ) ‘ p = _
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi, successorSectionColumn_value hi hp',
    usubaIterationPrefix_section (mem_succ_self k) hik]

theorem usubaTower_section_first {k p : V} [IsOrdinal k] (hp : p ∈ (T).P k) :
    ((T).sectionMap k (succ k)) ‘ p = ⟨p, ∅⟩ₖ := by
  rw [usubaTower_section_succ (subset_refl k) hp, (T).section_self k inferInstance p hp]

theorem usubaTower_inverse_condition {θ f : V} [IsOrdinal θ]
    (hz : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
    (hf : IsIterationTable θ f) (hm : ∀ i ∈ θ, f ‘ i ∈ (T).P i)
    (hc : ∀ j ∈ θ, ∀ i ∈ j, ((T).projection i j) ‘ (f ‘ j) = f ‘ i) :
    f ∈ (T).P θ := by
  rw [usubaTower_P_limit hz hs]
  refine (mem_forcingInverseLimit_iff _ _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · apply hf.mem_function
    intro i hi
    apply (usubaIterationPrefix_valid θ).subset_universe i hi
    rw [usubaIterationPrefix_P hi]
    exact hm i hi
  · intro i hi
    rw [usubaIterationPrefix_P hi]
    exact hm i hi
  · intro j hj i hij hi
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    rw [usubaIterationPrefix_projection hj (IsOrdinal.toIsTransitive.transitive _ hij)]
    exact hc j hj i hij

end ZFVP

