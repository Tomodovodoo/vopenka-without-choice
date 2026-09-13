import ZFVP.SetTheory.CorrectnessSupport

/-! The internally coded classes C(n) of Sigma_n-correct rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cnFormula : ℕ → SetTheorySemisentence 1
  | 0 => IsOrdinal.dfn
  | k + 1 => piCorrectRankStageFormula (k + 1)

theorem cnFormula_pi_bound (k : ℕ) : IsPiFormula (max 2 k) (cnFormula k) := by
  cases k with
  | zero => exact .bounded isOrdinalFormula_bounded
  | succ k => exact piCorrectRankStageFormula_bound (k + 1)

theorem cnFormula_pi {k : ℕ} (hk : 2 ≤ k) : IsPiFormula k (cnFormula k) := by
  simpa only [Nat.max_eq_right hk] using cnFormula_pi_bound k

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def Cn : ℕ → V → Prop
  | 0, α => IsOrdinal α
  | k + 1, α => IsOrdinal α ∧ CodedSigmaCorrect k (hierarchy α)

theorem cn_successor_iff (k : ℕ) (α : V) : Cn (k + 1) α ↔ IsCorrectRankStage (k + 1) α :=
  (correctRankStage_iff_codedCorrect k α).symm

theorem eval_cnFormula (k : ℕ) (α : V) : (cnFormula k).Evalb ![α] ↔ Cn k α := by
  cases k with
  | zero => simp [cnFormula, Cn]
  | succ k => exact (eval_piCorrectRankStageFormula (k + 1) α).trans (cn_successor_iff k α).symm

instance cnFormula_defined (k : ℕ) : ℒₛₑₜ-predicate[V] (Cn k) via cnFormula k :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (cnFormula k).Evalb v ↔ Cn k (v 0)
    rw [← hv]
    exact eval_cnFormula k (v 0)⟩

instance cn_definable (k : ℕ) : ℒₛₑₜ-predicate[V] (Cn k) := (cnFormula_defined k).to_definable

theorem Cn.ordinal {k : ℕ} {α : V} (h : Cn k α) : IsOrdinal α := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem Cn.of_le {k l : ℕ} {α : V} (h : Cn l α) (hkl : k ≤ l) : Cn k α := by
  cases k with
  | zero => exact h.ordinal
  | succ k =>
    cases l with
    | zero => omega
    | succ l => exact (cn_successor_iff k α).mpr (((cn_successor_iff l α).mp h).of_le hkl)

theorem cn_unbounded (k : ℕ) (γ : V) [IsOrdinal γ] : ∃ δ : V, γ ∈ δ ∧ Cn k δ := by
  cases k with
  | zero => exact ⟨succ γ, by simp, show IsOrdinal (succ γ) from inferInstance⟩
  | succ k =>
    obtain ⟨δ, hγ, hδ⟩ := correctRankStage_unbounded (k + 1) γ
    exact ⟨δ, hγ, (cn_successor_iff k δ).mpr hδ⟩

theorem cn_closed (k : ℕ) {δ : V} [IsOrdinal δ] (hδ : IsNonempty δ)
    (h : ∀ ξ ∈ δ, ∃ α ∈ δ, ξ ∈ α ∧ Cn k α) : Cn k δ := by
  cases k with
  | zero => exact show IsOrdinal δ from inferInstance
  | succ k =>
    apply (cn_successor_iff k δ).mpr
    apply correctRankStage_closed (k + 1) hδ
    intro ξ hξ
    obtain ⟨α, hα, hξα, hD⟩ := h ξ hξ
    exact ⟨α, hα, hξα, (cn_successor_iff k α).mp hD⟩

theorem Cn.sigma_correct {k n : ℕ} {α : V} (hα : Cn (k + 1) α)
    {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula (k + 1) φ) (b : Fin n → SetDomain (hierarchy α)) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val) := ((cn_successor_iff k α).mp hα).sigma_correct hφ b

theorem Cn.pi_correct {k n : ℕ} {α : V} (hα : Cn (k + 1) α)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (k + 1) φ) (b : Fin n → SetDomain (hierarchy α)) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val) := ((cn_successor_iff k α).mp hα).pi_correct hφ b

theorem Cn.formula_absolute {k m : ℕ} {δ : V} (hδ : Cn (m + 1) δ) (hkm : max 2 k ≤ m + 1)
    (α : SetDomain (hierarchy δ)) : (cnFormula k).Evalb ![α] ↔ Cn k α.val := by
  have hp := hδ.pi_correct ((cnFormula_pi_bound k).mono hkm) ![α]
  have he : (fun i : Fin 1 ↦ (![α] i).val) = ![α.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [he] at hp
  exact hp.trans (eval_cnFormula k α.val)

theorem Cn.rank_formula_correct {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    (α x : SetDomain (hierarchy δ)) : piOneRankFormula.Evalb ![α, x] ↔ α.val = rank x.val := by
  have hp := hδ.pi_correct (piOneRankFormula_piOne.mono (Nat.succ_le_succ (Nat.zero_le k))) ![α, x]
  have he : (fun i : Fin 2 ↦ (![α, x] i).val) = ![α.val, x.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [he] at hp
  exact hp.trans (eval_piOneRankFormula α.val x.val)

theorem Cn.hierarchy_formula_correct {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    (A α : SetDomain (hierarchy δ)) :
    piOneHierarchyFormula.Evalb ![A, α] ↔ IsOrdinal α.val ∧ A.val = hierarchy α.val := by
  have hp := hδ.pi_correct (piOneHierarchyFormula_piOne.mono (Nat.succ_le_succ (Nat.zero_le k))) ![A, α]
  have he : (fun i : Fin 2 ↦ (![A, α] i).val) = ![A.val, α.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [he] at hp
  exact hp.trans (eval_piOneHierarchyFormula A.val α.val)

end ZFVP
