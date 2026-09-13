import ZFVP.SetTheory.Collection
import ZFVP.SetTheory.NaturalIteration

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_union_ordinal (α β : V) [IsOrdinal α] [IsOrdinal β] : IsOrdinal (α ∪ β) := by
  apply IsOrdinal.of_transitive_of_isOrdinal IsTransitive.union
  intro x hx
  rcases mem_union_iff.mp hx with hx | hx
  · exact IsOrdinal.of_mem hx
  · exact IsOrdinal.of_mem hx

noncomputable def leastWitnessStageOrZero (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x : V) : V := by
  classical
  exact if h : ∃ y, R x y then Classical.choose! (leastWitnessStage_existsUnique R hR x h) else 0

theorem leastWitnessStageOrZero_eq_iff (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x α : V) :
    α = leastWitnessStageOrZero R hR x ↔
      IsLeastWitnessStage R x α ∨ (¬∃ y, R x y) ∧ α = 0 := by
  classical
  by_cases h : ∃ y, R x y
  · have hs := Classical.choose!_spec (leastWitnessStage_existsUnique R hR x h)
    simp only [h, not_true_eq_false, false_and, or_false, leastWitnessStageOrZero, ↓reduceDIte]
    constructor
    · rintro rfl
      exact hs
    · intro hα
      exact (leastWitnessStage_existsUnique R hR x h).unique hα hs
  · have hn : ¬IsLeastWitnessStage R x α := by
      intro hα
      obtain ⟨y, _, hy⟩ := hα.2.1
      exact h ⟨y, hy⟩
    simp [leastWitnessStageOrZero, h, hn]

instance leastWitnessStageOrZero_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-function₁ (leastWitnessStageOrZero R hR) := by
  have := isLeastWitnessStage_definable R hR
  have h : ℒₛₑₜ-relation (fun α x : V ↦ IsLeastWitnessStage R x α ∨ (¬∃ y, R x y) ∧ α = 0) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  exact leastWitnessStageOrZero_eq_iff R hR (v 1) (v 0)

theorem leastWitnessStageOrZero_spec (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (x : V) (hx : ∃ y, R x y) : IsLeastWitnessStage R x (leastWitnessStageOrZero R hR x) := by
  have h := (leastWitnessStageOrZero_eq_iff R hR x _).mp rfl
  exact h.resolve_right (fun hh ↦ hh.1 hx)

instance leastWitnessStageOrZero_ordinal (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x : V) :
    IsOrdinal (leastWitnessStageOrZero R hR x) := by
  rcases (leastWitnessStageOrZero_eq_iff R hR x _).mp rfl with h | ⟨_, heq⟩
  · exact h.1
  · rw [heq]
    infer_instance

noncomputable def witnessBoundingStep (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (α : V) : V :=
  succ (α ∪ ⋃ˢ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α))

instance witnessBoundingStep_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-function₁ (witnessBoundingStep R hR) := by
  unfold witnessBoundingStep
  definability

instance witnessBoundingStep_ordinal (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (α : V)
    [IsOrdinal α] : IsOrdinal (witnessBoundingStep R hR α) := by
  have : IsOrdinal (⋃ˢ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α)) :=
    IsOrdinal.sUnion (by
      intro β hβ
      obtain ⟨x, _, rfl⟩ := (repl_spec (show ℒₛₑₜ-function₁ (leastWitnessStageOrZero R hR) from by definability)).mp hβ
      infer_instance)
  unfold witnessBoundingStep
  have := ordinal_union_ordinal α (⋃ˢ repl (leastWitnessStageOrZero R hR) (leastWitnessStageOrZero_definable R hR) (hierarchy α))
  infer_instance

theorem witnessBoundingStep_gt (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (α : V)
    [IsOrdinal α] : α ∈ witnessBoundingStep R hR α := by
  have : IsOrdinal (⋃ˢ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α)) :=
    IsOrdinal.sUnion (by
      intro β hβ
      obtain ⟨x, _, rfl⟩ := (repl_spec (show ℒₛₑₜ-function₁ (leastWitnessStageOrZero R hR) from by definability)).mp hβ
      infer_instance)
  have := ordinal_union_ordinal α (⋃ˢ repl (leastWitnessStageOrZero R hR) (leastWitnessStageOrZero_definable R hR) (hierarchy α))
  apply mem_succ_iff.mpr
  exact IsOrdinal.subset_iff.mp (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))

theorem witnessBoundingStep_spec (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (α : V)
    [IsOrdinal α] {x : V} (hx : x ∈ hierarchy α) (hex : ∃ y, R x y) :
    ∃ y ∈ hierarchy (witnessBoundingStep R hR α), R x y := by
  let β := leastWitnessStageOrZero R hR x
  have : IsOrdinal β := leastWitnessStageOrZero_ordinal R hR x
  obtain ⟨y, hy, hxy⟩ := (leastWitnessStageOrZero_spec R hR x hex).2.1
  have hβ : β ∈ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α) :=
    (repl_spec (show ℒₛₑₜ-function₁ (leastWitnessStageOrZero R hR) from by definability)).mpr ⟨x, hx, rfl⟩
  have hsub : β ⊆ witnessBoundingStep R hR α := by
    intro z hz
    exact mem_succ_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inr (subset_sUnion_of_mem hβ z hz))))
  exact ⟨y, hierarchy_mono hsub y hy, hxy⟩

def IsWitnessClosed (R : V → V → Prop) (α : V) : Prop :=
  ∀ x ∈ hierarchy α, (∃ y, R x y) → ∃ y ∈ hierarchy α, R x y

theorem isWitnessClosed_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-predicate (IsWitnessClosed R) := by
  unfold IsWitnessClosed
  definability

theorem witnessClosed_above (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (γ : V) [IsOrdinal γ] :
    ∃ δ : V, IsOrdinal δ ∧ γ ∈ δ ∧ (∀ ξ ∈ δ, succ ξ ∈ δ) ∧ IsWitnessClosed R δ := by
  let F := witnessBoundingStep R hR
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let a := naturalIteration F hF γ
  have ha (n : V) (hn : n ∈ (ω : V)) : IsOrdinal (a n) :=
    naturalIteration_invariant F hF γ IsOrdinal (by definability) inferInstance
      (fun x hx ↦ by have : IsOrdinal x := hx; exact witnessBoundingStep_ordinal R hR x) n hn
  have hsucc (n : V) (hn : n ∈ (ω : V)) : a (succ n) = F (a n) := naturalIteration_succ F hF γ hn
  have hinc (n : V) (hn : n ∈ (ω : V)) : a n ∈ a (succ n) := by
    have : IsOrdinal (a n) := ha n hn
    rw [hsucc n hn]
    exact witnessBoundingStep_gt R hR _
  let g := naturalIterationGraph F hF γ
  have hval (n : V) (hn : n ∈ (ω : V)) : g ‘ n = a n := naturalIterationGraph_value F hF γ hn
  let δ := ⋃ˢ range g
  have hord : IsOrdinal δ := IsOrdinal.sUnion (by
    intro α hα
    obtain ⟨n, hnα⟩ := mem_range_iff.mp hα
    have hn : n ∈ (ω : V) := by simpa only [g, domain_naturalIterationGraph] using mem_domain_of_kpair_mem hnα
    rw [← value_eq_of_kpair_mem hnα, hval n hn]
    exact ha n hn)
  have hstage (n : V) (hn : n ∈ (ω : V)) : a n ∈ δ := by
    have hs : a (succ n) ∈ range g := by
      rw [← hval (succ n) (ω_succ_closed hn)]
      exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [g, domain_naturalIterationGraph] using ω_succ_closed hn))
    exact mem_sUnion_iff.mpr ⟨a (succ n), hs, hinc n hn⟩
  have hcof (ξ : V) (hξ : ξ ∈ δ) : ∃ n ∈ (ω : V), ξ ∈ a n := by
    obtain ⟨α, hα, hξα⟩ := mem_sUnion_iff.mp hξ
    obtain ⟨n, hnα⟩ := mem_range_iff.mp hα
    have hn : n ∈ (ω : V) := by simpa only [g, domain_naturalIterationGraph] using mem_domain_of_kpair_mem hnα
    exact ⟨n, hn, ((value_eq_of_kpair_mem hnα).symm.trans (hval n hn)) ▸ hξα⟩
  refine ⟨δ, hord, ?_, ?_, ?_⟩
  · simpa only [a, naturalIteration_zero] using hstage 0 (show (0 : V) ∈ ω by simp)
  · intro ξ hξ
    obtain ⟨n, hn, hξn⟩ := hcof ξ hξ
    have : IsOrdinal (a n) := ha n hn
    have : IsOrdinal ξ := IsOrdinal.of_mem hξn
    have hsub : succ ξ ⊆ a n := by
      intro z hz
      rcases mem_succ_iff.mp hz with rfl | hz
      · exact hξn
      · exact IsOrdinal.toIsTransitive.mem_trans hz hξn
    rcases IsOrdinal.subset_iff.mp hsub with heq | hlt
    · exact heq.symm ▸ hstage n hn
    · exact IsOrdinal.toIsTransitive.mem_trans hlt (hstage n hn)
  · intro x hx hex
    obtain ⟨n, hn, hrank⟩ := hcof (rank x) ((mem_hierarchy_iff_rank_mem _ _).mp hx)
    have : IsOrdinal (a n) := ha n hn
    have hxstage : x ∈ hierarchy (a n) := (mem_hierarchy_iff_rank_mem _ _).mpr hrank
    obtain ⟨y, hy, hxy⟩ := witnessBoundingStep_spec R hR (a n) hxstage hex
    have : IsOrdinal (a (succ n)) := ha (succ n) (ω_succ_closed hn)
    have hsub : a (succ n) ⊆ δ := IsOrdinal.toIsTransitive.transitive _ (hstage (succ n) (ω_succ_closed hn))
    change y ∈ hierarchy (F (a n)) at hy
    rw [← hsucc n hn] at hy
    exact ⟨y, hierarchy_mono hsub y hy, hxy⟩

theorem witnessClosed_of_cofinal (R : V → V → Prop) {δ : V} [IsOrdinal δ]
    (h : ∀ ξ ∈ δ, ∃ α ∈ δ, ξ ∈ α ∧ IsWitnessClosed R α) : IsWitnessClosed R δ := by
  intro x hx hex
  obtain ⟨α, hα, hrank, hclosed⟩ := h (rank x) ((mem_hierarchy_iff_rank_mem _ _).mp hx)
  have : IsOrdinal α := IsOrdinal.of_mem hα
  obtain ⟨y, hy, hxy⟩ := hclosed x ((mem_hierarchy_iff_rank_mem _ _).mpr hrank) hex
  exact ⟨y, hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hα) y hy, hxy⟩

end ZFVP
