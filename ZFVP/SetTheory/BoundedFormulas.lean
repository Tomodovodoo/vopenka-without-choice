import ZFVP.SetTheory.Relativization
import Foundation.FirstOrder.SetTheory.Ordinal

/-! Bounded membership quantifiers in externally finite set-theory syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSetAll {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence n :=
  .all (.or (.nrel Language.Set.Rel.mem ![.bvar 0, Rew.bShift t]) φ)

def boundedSetExs {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence n :=
  .exs (.and (.rel Language.Set.Rel.mem ![.bvar 0, Rew.bShift t]) φ)

inductive IsBoundedSetFormula : {n : ℕ} → SetTheorySemisentence n → Prop
  | verum {n} : IsBoundedSetFormula (.verum : SetTheorySemisentence n)
  | falsum {n} : IsBoundedSetFormula (.falsum : SetTheorySemisentence n)
  | rel {n k} (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) :
      IsBoundedSetFormula (.rel r ts)
  | nrel {n k} (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) :
      IsBoundedSetFormula (.nrel r ts)
  | and {n} {φ ψ : SetTheorySemisentence n} :
      IsBoundedSetFormula φ → IsBoundedSetFormula ψ → IsBoundedSetFormula (.and φ ψ)
  | or {n} {φ ψ : SetTheorySemisentence n} :
      IsBoundedSetFormula φ → IsBoundedSetFormula ψ → IsBoundedSetFormula (.or φ ψ)
  | all {n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      IsBoundedSetFormula φ → IsBoundedSetFormula (boundedSetAll t φ)
  | exs {n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      IsBoundedSetFormula φ → IsBoundedSetFormula (boundedSetExs t φ)

theorem IsBoundedSetFormula.neg {n : ℕ} {φ : SetTheorySemisentence n}
    (h : IsBoundedSetFormula φ) : IsBoundedSetFormula (∼φ) := by
  induction h with
  | verum => exact .falsum
  | falsum => exact .verum
  | rel r ts => exact .nrel r ts
  | nrel r ts => exact .rel r ts
  | and hφ hψ ihφ ihψ => exact .or ihφ ihψ
  | or hφ hψ ihφ ihψ => exact .and ihφ ihψ
  | all t hφ ihφ => exact .exs t ihφ
  | exs t hφ ihφ => exact .all t ihφ

variable {V : Type*} [SetStructure V]

theorem eval_boundedSetAll {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1))
    (b : Fin n → V) : (boundedSetAll t φ).Evalb b ↔ ∀ y ∈ t.val b Empty.elim, φ.Evalb (y :> b) := by
  change (∀ y : V, y ∉ (Rew.bShift t).val (y :> b) Empty.elim ∨ φ.Evalb (y :> b)) ↔ _
  simp only [Semiterm.val_bShift]
  constructor
  · intro h y hy
    exact (h y).resolve_left (fun hn ↦ hn hy)
  · intro h y
    by_cases hy : y ∈ t.val b Empty.elim
    · exact Or.inr (h y hy)
    · exact Or.inl hy

theorem eval_boundedSetExs {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1))
    (b : Fin n → V) : (boundedSetExs t φ).Evalb b ↔ ∃ y ∈ t.val b Empty.elim, φ.Evalb (y :> b) := by
  change (∃ y : V, y ∈ (Rew.bShift t).val (y :> b) Empty.elim ∧ φ.Evalb (y :> b)) ↔ _
  simp only [Semiterm.val_bShift]

theorem bounded_formula_absolute (A : V) [hA : IsTransitive A] {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → SetDomain A) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val) := by
  have ht {n : ℕ} (b : Fin n → SetDomain A) (t : SetTheorySemiterm Empty n) :
      (t.val b Empty.elim).val = t.val (fun i ↦ (b i).val) Empty.elim := by
    cases t with
    | bvar i => rfl
    | fvar e => exact Empty.elim e
    | func f ts => exact Empty.elim f
  induction hφ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_rel, Structure.rel, Function.comp_def, ← ht]
    · exact Subtype.ext_iff
    · rfl
  | nrel r ts =>
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_nrel, Structure.rel, Function.comp_def, ← ht]
    · exact not_congr Subtype.ext_iff
    · rfl
  | and hφ hψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or hφ hψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | @all n t φ hφ ih =>
    rw [eval_boundedSetAll, eval_boundedSetAll]
    constructor
    · intro h y hy
      have hyA : y ∈ A := hA.transitive (t.val b Empty.elim).val (t.val b Empty.elim).property y ((ht b t).symm ▸ hy)
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      have htrue := (ih (⟨y, hyA⟩ :> b)).mp (h ⟨y, hyA⟩ hy')
      rw [setDomain_val_vecCons A (⟨y, hyA⟩ : SetDomain A) b] at htrue
      exact htrue
    · intro h y hy
      apply (ih (y :> b)).mpr
      rw [setDomain_val_vecCons A y b]
      exact h y.val ((ht b t) ▸ hy)
  | @exs n t φ hφ ih =>
    rw [eval_boundedSetExs, eval_boundedSetExs]
    constructor
    · rintro ⟨y, hy, htrue⟩
      refine ⟨y.val, (ht b t) ▸ hy, ?_⟩
      have hh := (ih (y :> b)).mp htrue
      rw [setDomain_val_vecCons A y b] at hh
      exact hh
    · rintro ⟨y, hy, htrue⟩
      have hyA : y ∈ A := hA.transitive (t.val b Empty.elim).val (t.val b Empty.elim).property y ((ht b t).symm ▸ hy)
      have hy' : y ∈ (t.val b Empty.elim).val := (ht b t).symm ▸ hy
      refine ⟨⟨y, hyA⟩, hy', (ih (⟨y, hyA⟩ :> b)).mpr ?_⟩
      rw [setDomain_val_vecCons A (⟨y, hyA⟩ : SetDomain A) b]
      exact htrue

end ZFVP
