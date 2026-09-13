import ZFVP.ModelTheory.UsubaIterationStages

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)
local notation "C" => usubaCodeSequence (V := V)

noncomputable def usubaTowerLift (i j : V) : V :=
  (forcingCodeL (usubaIterationRec j)) ‘ ⟨i, j⟩ₖ

instance usubaTowerLift_definable : ℒₛₑₜ-function₂[V] usubaTowerLift := by
  unfold usubaTowerLift
  definability

theorem usubaIterationPrefix_lift {θ i j : V} [IsOrdinal θ] [IsOrdinal i]
    (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingCodeL (usubaIterationPrefix θ)) ‘ ⟨i, j⟩ₖ = usubaTowerLift i j := by
  have := IsOrdinal.of_mem hj
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  exact (((C).valid j inferInstance).tableL.value_of_subset ((C).prefix_valid θ).tableL
    ((C).prefix_extends hj).subL (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

theorem usubaTowerLift_spec {i j r b : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hr : r ∈ (T).P j) (hb : b ∈ (T).P i)
    (hbr : ⟨b, ((T).projection i j) ‘ r⟩ₖ ∈ (T).R i) :
    (usubaTowerLift i j) ‘ ⟨r, b⟩ₖ ∈ (T).P j ∧
      ⟨(usubaTowerLift i j) ‘ ⟨r, b⟩ₖ, r⟩ₖ ∈ (T).R j ∧
      ((T).projection i j) ‘ ((usubaTowerLift i j) ‘ ⟨r, b⟩ₖ) = b := by
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  have h := (usubaIterationPrefix_valid (succ j)).system.lifts.lift i hi j
    (mem_succ_self j) hij
  simp only [usubaIterationPrefix_P hi, usubaIterationPrefix_P (mem_succ_self j),
    usubaIterationPrefix_R hi, usubaIterationPrefix_R (mem_succ_self j),
    usubaIterationPrefix_projection (mem_succ_self j) hij,
    usubaIterationPrefix_lift (mem_succ_self j) hij] at h
  exact h r hr b hb hbr

theorem usubaTowerLift_commute {i k j r b : V} [IsOrdinal i] [IsOrdinal k] [IsOrdinal j]
    (hik : i ⊆ k) (hkj : k ⊆ j) (hr : r ∈ (T).P j) (hb : b ∈ (T).P i)
    (hbr : ⟨b, ((T).projection i j) ‘ r⟩ₖ ∈ (T).R i) :
    ((T).projection k j) ‘ ((usubaTowerLift i j) ‘ ⟨r, b⟩ₖ) =
      (usubaTowerLift i k) ‘ ⟨((T).projection k j) ‘ r, b⟩ₖ := by
  have hij : i ⊆ j := subset_trans hik hkj
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  have hk : k ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hkj)
  have h := (usubaIterationPrefix_valid (succ j)).system.lifts.commute i hi k hk j
    (mem_succ_self j) hik hkj
  simp only [usubaIterationPrefix_P hi, usubaIterationPrefix_P (mem_succ_self j),
    usubaIterationPrefix_R hi, usubaIterationPrefix_projection (mem_succ_self j) hij,
    usubaIterationPrefix_projection (mem_succ_self j) hkj,
    usubaIterationPrefix_lift (mem_succ_self j) hij, usubaIterationPrefix_lift hk hik]
    at h
  exact h r hr b hb hbr

theorem usubaTowerLift_successor_value {i k r b : V} [IsOrdinal i] [IsOrdinal k]
    (hik : i ⊆ k) (hr : r ∈ (T).P (succ k)) (hb : b ∈ (T).P i) :
    (usubaTowerLift i (succ k)) ‘ ⟨r, b⟩ₖ =
      successorForcingLiftValue (usubaTowerLift i k) r b := by
  have hi : i ∈ succ k := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hik)
  have hr' := hr
  rw [usubaTower_P_succ k] at hr'
  have hb' : b ∈ (forcingCodeP (usubaIterationPrefix (succ k))) ‘ i := by
    rwa [usubaIterationPrefix_P hi]
  unfold usubaTowerLift at ⊢
  rw [usubaIterationRec_succ]
  simp only [usubaIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeL_code, forcingMatrixNext_column hi,
    usubaIterationPrefix_P (mem_succ_self k), usubaIterationPrefix_R (mem_succ_self k),
    successorLiftColumn_value hi hr' hb', usubaIterationPrefix_lift (mem_succ_self k) hik]
  rfl

theorem usubaTowerLift_successor_pair {i k r b : V} [IsOrdinal i] [IsOrdinal k]
    (hik : i ⊆ k) (hr : r ∈ (T).P (succ k)) (hb : b ∈ (T).P i) :
    (usubaTowerLift i (succ k)) ‘ ⟨r, b⟩ₖ =
      ⟨(usubaTowerLift i k) ‘ ⟨kpair.π₁ r, b⟩ₖ, kpair.π₂ r⟩ₖ := by
  rw [usubaTowerLift_successor_value hik hr hb]
  rfl

end ZFVP
