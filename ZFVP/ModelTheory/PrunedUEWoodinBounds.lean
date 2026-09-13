import ZFVP.ModelTheory.CountablePrunedGroundModel
import ZFVP.SetTheory.CnExtendibleWoodinSupercompact
import ZFVP.SetTheory.CnExtendibleHighCriticalWoodin
import ZFVP.SetTheory.CnExtendibleDownward

/-! Ground bounds obtained from the actual UE sentences.
The pruned theory supplies UE through the instance below.
These results apply to arbitrary membership models, including externally
ill-founded models. No forcing or preservation assertion is assumed.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
instance prunedUE_models_unboundedExtendibility (V : Type*)
    [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory] :
    V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory :=
  ⟨fun _ hφ ↦ Theory.models V zfUEVPNoRankBerkeleyTheory (Or.inr (Or.inr hφ))⟩

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

theorem prunedUE_cnExtendible_unbounded (n : ℕ) (α : V) (hα : IsOrdinal α) :
    ∃ κ : V, α ∈ κ ∧ IsCnExtendible (n + 1) κ := by
  have hUE : V↓[ℒₛₑₜ] ⊧ unboundedExtendibilitySentence (n + 1) :=
    Theory.models V unboundedExtendibilityTheory ⟨n, rfl⟩
  exact (eval_unboundedExtendibilitySentence (n + 1)).mp hUE α hα

/-- One UE instance supplies any prescribed finite extendibility and
correctness levels, together with both Woodin witness properties. -/
theorem prunedUE_exists_correctWoodin_above (n r : ℕ) (α : V) (hα : IsOrdinal α) :
    ∃ Ω : V, α ∈ Ω ∧ IsCnExtendible (n + 1) Ω ∧ Cn r Ω ∧
      IsWoodinSupercompact Ω ∧ HasHighCriticalWoodinWitnesses Ω := by
  let b := max (max n r) (max woodinSupercompactComplexity.val highCriticalWoodinComplexity.val)
  obtain ⟨Ω, hαΩ, hΩ⟩ := prunedUE_cnExtendible_unbounded (V := V) b α hα
  have hn : n ≤ b := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  have hr : r ≤ b := (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  have hW : woodinSupercompactComplexity.val ≤ b :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hH : highCriticalWoodinComplexity.val ≤ b :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact ⟨Ω, hαΩ, hΩ.of_le hn, hΩ.cn.of_le (hr.trans (Nat.le_add_right _ 3)),
    IsCnExtendible.woodinSupercompact (hΩ.of_le hW),
    IsCnExtendible.highCriticalWoodin (hΩ.of_le hH)⟩

/-- Finite collections of construction parameters may be packed into `a`.
The chosen ambient rank contains that actual set and exceeds `α`. -/
theorem prunedUE_exists_correctWoodin_containing (n r : ℕ) (α a : V) (hα : IsOrdinal α) :
    ∃ Ω : V, α ∈ Ω ∧ a ∈ hierarchy Ω ∧ IsCnExtendible (n + 1) Ω ∧ Cn r Ω ∧
      IsWoodinSupercompact Ω ∧ HasHighCriticalWoodinWitnesses Ω := by
  let := hα
  let := ordinal_union_ordinal α (rank a)
  obtain ⟨Ω, hΩ, hE, hC, hW, hH⟩ :=
    prunedUE_exists_correctWoodin_above (V := V) n r (α ∪ rank a) inferInstance
  let := hE.1.1
  have hαΩ : α ∈ Ω := ordinal_mem_of_subset_mem (subset_union_left α (rank a)) hΩ
  have hraΩ : rank a ∈ Ω := ordinal_mem_of_subset_mem (subset_union_right α (rank a)) hΩ
  exact ⟨Ω, hαΩ, (mem_hierarchy_iff_rank_mem _ _).mpr hraΩ, hE, hC, hW, hH⟩

end ZFVP
