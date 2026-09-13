import ZFVP.SetTheory.CorrectDomainClosure
import ZFVP.SetTheory.UniformRank

/-! Definable closed unbounded classes of recursively correct rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def correctRankStageFormula (k : ℕ) : SetTheorySemisentence 1 :=
  f“α. !IsOrdinal.dfn α ∧ !(correctDomainFormula k) (!hierarchyFormula α)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCorrectRankStage (k : ℕ) (α : V) : Prop := IsOrdinal α ∧ CorrectDomain k (hierarchy α)

instance correctRankStageFormula_defined (k : ℕ) :
    ℒₛₑₜ-predicate[V] (IsCorrectRankStage k) via correctRankStageFormula k :=
  ⟨fun v ↦ by simp [correctRankStageFormula, IsCorrectRankStage]⟩

instance isCorrectRankStage_definable (k : ℕ) : ℒₛₑₜ-predicate[V] (IsCorrectRankStage k) :=
  (correctRankStageFormula_defined k).to_definable

theorem correctRankStage_unbounded (k : ℕ) (γ : V) [IsOrdinal γ] :
    ∃ δ : V, γ ∈ δ ∧ IsCorrectRankStage k δ := by
  obtain ⟨δ, hδ, hγ, _, _, hD, _⟩ := correctDomain_witnessClosed_above k
    (fun _ _ : V ↦ False) (by definability) γ
  exact ⟨δ, hγ, hδ, hD⟩

theorem IsCorrectRankStage.of_le {k l : ℕ} {α : V} (h : IsCorrectRankStage l α) (hkl : k ≤ l) :
    IsCorrectRankStage k α := ⟨h.1, h.2.of_le hkl⟩

theorem IsCorrectRankStage.omega_lt {k : ℕ} {α : V} (h : IsCorrectRankStage k α) : (ω : V) ∈ α := by
  let := h.1
  have hr := (mem_hierarchy_iff_rank_mem (ω : V) α).mp h.2.support.omega_mem
  simpa only [rank_of_ordinal] using hr

theorem correctRankStage_closed (k : ℕ) {δ : V} [IsOrdinal δ] (hδ : IsNonempty δ)
    (h : ∀ ξ ∈ δ, ∃ α ∈ δ, ξ ∈ α ∧ IsCorrectRankStage k α) : IsCorrectRankStage k δ := by
  obtain ⟨ξ, hξ⟩ := hδ.nonempty
  obtain ⟨α, hα, _, hDα⟩ := h ξ hξ
  have hω : (ω : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans hDα.omega_lt hα
  have hlim : ∀ ξ ∈ δ, succ ξ ∈ δ := by
    intro ξ hξ
    obtain ⟨β, hβ, hξβ, hDβ⟩ := h ξ hξ
    let := hDβ.1
    let := IsOrdinal.of_mem hξβ
    have hsub : succ ξ ⊆ β := by
      intro z hz
      rcases mem_succ_iff.mp hz with rfl | hz
      · exact hξβ
      · exact IsOrdinal.toIsTransitive.mem_trans hz hξβ
    exact ordinal_mem_of_subset_mem hsub hβ
  exact ⟨inferInstance, correctDomain_of_cofinal k hω hlim (fun ξ hξ ↦ by
    obtain ⟨α, hα, hξα, hD⟩ := h ξ hξ
    exact ⟨α, hα, hξα, hD.2⟩)⟩

theorem IsCorrectRankStage.sigma_correct {k n : ℕ} {α : V} (hα : IsCorrectRankStage (k + 1) α)
    {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula (k + 1) φ) (b : Fin n → SetDomain (hierarchy α)) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val) := by
  have hb := standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  exact (membershipSatisfies_encode hα.2.nonempty φ b).symm.trans
    (hα.2.standard_sigma_correct hφ (fun i ↦ (b i).val) hb)

theorem IsCorrectRankStage.pi_correct {k n : ℕ} {α : V} (hα : IsCorrectRankStage (k + 1) α)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (k + 1) φ) (b : Fin n → SetDomain (hierarchy α)) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val) := by
  have hb := standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  exact (membershipSatisfies_encode hα.2.nonempty φ b).symm.trans
    (hα.2.standard_pi_correct hφ (fun i ↦ (b i).val) hb)

end ZFVP
