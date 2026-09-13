import ZFVP.SetTheory.ChoicelessExtendibleSupercompact
import ZFVP.ModelTheory.CriticalPointCardinal

/-! Removing the prescribed lower bound on the critical point.
Cardinality follows from the small embedding witnesses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def choicelessExtendibleFormula (n : ℕ) : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ (∃ z, z ∈ κ) ∧ ∀ α ∈ κ, !(alphaChoicelessExtendibleFormula n) α κ”

def choicelessSupercompactFormula (n : ℕ) : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ (∃ z, z ∈ κ) ∧ ∀ α ∈ κ, !(alphaChoicelessSupercompactFormula n) α κ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsChoicelessExtendible (n : ℕ) (κ : V) : Prop :=
  IsOrdinal κ ∧ IsNonempty κ ∧ ∀ α ∈ κ, IsAlphaChoicelessExtendible n α κ

def IsChoicelessSupercompact (n : ℕ) (κ : V) : Prop :=
  IsOrdinal κ ∧ IsNonempty κ ∧ ∀ α ∈ κ, IsAlphaChoicelessSupercompact n α κ

instance choicelessExtendibleFormula_defined (n : ℕ) :
    ℒₛₑₜ-predicate[V] (IsChoicelessExtendible n) via choicelessExtendibleFormula n :=
  ⟨fun v ↦ by
    simp [choicelessExtendibleFormula, IsChoicelessExtendible]
    intro _ _
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx⟩⟩⟩

instance choicelessSupercompactFormula_defined (n : ℕ) :
    ℒₛₑₜ-predicate[V] (IsChoicelessSupercompact n) via choicelessSupercompactFormula n :=
  ⟨fun v ↦ by
    simp [choicelessSupercompactFormula, IsChoicelessSupercompact]
    intro _ _
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx⟩⟩⟩

instance choicelessExtendible_definable (n : ℕ) : ℒₛₑₜ-predicate[V] (IsChoicelessExtendible n) :=
  (choicelessExtendibleFormula_defined n).to_definable

instance choicelessSupercompact_definable (n : ℕ) : ℒₛₑₜ-predicate[V] (IsChoicelessSupercompact n) :=
  (choicelessSupercompactFormula_defined n).to_definable

theorem IsChoicelessExtendible.supercompact {n : ℕ} {κ : V}
    (h : IsChoicelessExtendible (n + 2) κ) : IsChoicelessSupercompact (n + 2) κ :=
  ⟨h.1, h.2.1, fun α hα ↦ (h.2.2 α hα).supercompact⟩

theorem IsChoicelessSupercompact.initial {n : ℕ} {κ : V}
    (h : IsChoicelessSupercompact (n + 1) κ) : IsInitialOrdinal κ := by
  let := h.1
  refine ⟨h.1, ?_⟩
  intro α hα hinj
  obtain ⟨μ, hκμ, hμ⟩ := cn_unbounded (n + 1) κ
  let := hμ.ordinal
  obtain ⟨_, ν, x, f, c, hνκ, hν, _, hf, hc, hαc, _⟩ :=
    (h.2.2 α hα).2.2 μ hμ hκμ ω (ordinal_subset_hierarchy μ _ hμ.omega_lt)
  let := hν.ordinal
  let := hc.ordinal
  have hcν : c ∈ ν := ordinal_mem_hierarchy_iff.mp hc.mem_domain
  have hcκ : c ∈ κ := IsOrdinal.toIsTransitive.mem_trans hcν hνκ
  have hi := rankEmbedding_criticalPoint_initial hν hμ hf hc
  exact hi.2 α hαc ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hcκ)).trans hinj)

theorem IsChoicelessSupercompact.omega_lt {n : ℕ} {κ : V}
    (h : IsChoicelessSupercompact (n + 1) κ) : (ω : V) ∈ κ := by
  let := h.1
  obtain ⟨α, hα⟩ := h.2.1
  obtain ⟨μ, hκμ, hμ⟩ := cn_unbounded (n + 1) κ
  let := hμ.ordinal
  obtain ⟨_, ν, x, f, c, hνκ, hν, _, hf, hc, _, _⟩ :=
    (h.2.2 α hα).2.2 μ hμ hκμ ω (ordinal_subset_hierarchy μ _ hμ.omega_lt)
  let := hν.ordinal
  let := hc.ordinal
  let := hierarchy_transitive ν
  let := hierarchy_transitive μ
  let : IsSequenceSupport (hierarchy ν) := ((cn_successor_iff n ν).mp hν).2.support
  let : IsSequenceSupport (hierarchy μ) := ((cn_successor_iff n μ).mp hμ).2.support
  have hcν : c ∈ ν := ordinal_mem_hierarchy_iff.mp hc.mem_domain
  exact IsOrdinal.toIsTransitive.mem_trans (hc.omega_lt hf)
    (IsOrdinal.toIsTransitive.mem_trans hcν hνκ)

end ZFVP
