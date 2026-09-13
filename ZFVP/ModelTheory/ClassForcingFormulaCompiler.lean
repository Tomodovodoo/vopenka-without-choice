import ZFVP.ModelTheory.ClassForcingTowerFormula

/-! A fixed syntax compiler for the forcing relation of a class tower.

The input formulas are independent of the ground model. The correctness
theorem identifies the compiled formula with `towerFormula` whenever the
five input formulas define the stated tower data in that model. In
particular, this does not choose a new defining formula in each model.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingTermValueFormula {n : ℕ} :
    Semiterm ℒₛₑₜ Empty n → SetTheorySemisentence 2
  | .bvar i => f“x b. x = !value.dfn b (!(numeralFormula i.val))”
  | .fvar x => Empty.elim x
  | .func f _ => Empty.elim f

structure ClassForcingFormulaDictionary where
  condition : SetTheorySemisentence 1
  le : SetTheorySemisentence 2
  isName : SetTheorySemisentence 1
  equal : SetTheorySemisentence 3
  member : SetTheorySemisentence 3

namespace ClassForcingFormulaDictionary

def atomic (D : ClassForcingFormulaDictionary) {n k : ℕ}
    (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    SetTheorySemisentence 2 :=
  match r with
  | .eq => f“b p. !(D.equal) (!(forcingTermValueFormula (ts 0)) b)
      (!(forcingTermValueFormula (ts 1)) b) p”
  | .mem => f“b p. !(D.member) (!(forcingTermValueFormula (ts 0)) b)
      (!(forcingTermValueFormula (ts 1)) b) p”

def negate (D : ClassForcingFormulaDictionary) (F : SetTheorySemisentence 2) :
    SetTheorySemisentence 2 :=
  f“b p. !(D.condition) p ∧ ∀ q, !(D.condition) q → !(D.le) q p → ¬ !F b q”

def close (D : ClassForcingFormulaDictionary) (F : SetTheorySemisentence 2) :
    SetTheorySemisentence 2 :=
  f“b p. !(D.condition) p ∧ ∀ q, !(D.condition) q → !(D.le) q p →
    ∃ r, !F b r ∧ !(D.le) r q”

def compile (D : ClassForcingFormulaDictionary) :
    {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence 2
  | _, .verum => f“b p. !(D.condition) p”
  | _, .falsum => ⊥
  | _, .rel r ts => D.atomic r ts
  | _, .nrel r ts => D.negate (D.atomic r ts)
  | _, .and φ ψ => f“b p. !(D.compile φ) b p ∧ !(D.compile ψ) b p”
  | _, .or φ ψ => D.close f“b p. !(D.compile φ) b p ∨ !(D.compile ψ) b p”
  | n, .all φ => f“b p. !(D.condition) p ∧ ∀ x, !(D.isName) x →
      !(D.compile φ) (!assignmentPrependFormula (!(numeralFormula n)) b x) p”
  | n, .exs φ => D.close f“b p. ∃ x, !(D.isName) x ∧
      !(D.compile φ) (!assignmentPrependFormula (!(numeralFormula n)) b x) p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The same five formulas describe this model's tower. -/
structure Defines (D : ClassForcingFormulaDictionary) (T : DefinableForcingTower V) : Prop where
  condition : (ℒₛₑₜ-predicate[V] T.Condition via D.condition)
  le : (ℒₛₑₜ-relation[V] T.LE via D.le)
  isName : (ℒₛₑₜ-predicate[V] T.IsName via D.isName)
  equal : (ℒₛₑₜ-relation₃[V] T.ForcesEqual via D.equal)
  member : (ℒₛₑₜ-relation₃[V] T.ForcesMember via D.member)

instance forcingTermValueFormula_defined {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) :
    ℒₛₑₜ-function₁[V] (forcingTermValue t) via forcingTermValueFormula t := by
  cases t with
  | bvar i => exact ⟨fun v ↦ by simp [forcingTermValueFormula, forcingTermValue]⟩
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

variable {D : ClassForcingFormulaDictionary} {T : DefinableForcingTower V}

theorem atomic_defined (hD : D.Defines T) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    ℒₛₑₜ-relation (T.towerAtomic r ts) via D.atomic r ts := by
  let := hD.equal
  let := hD.member
  cases r <;> exact ⟨fun v ↦ by simp [atomic, DefinableForcingTower.towerAtomic]⟩

theorem negate_defined (hD : D.Defines T) (F : V → V → Prop)
    (φ : SetTheorySemisentence 2) (hφ : ℒₛₑₜ-relation F via φ) :
    ℒₛₑₜ-relation (fun b ↦ T.ClassNegation (F b)) via D.negate φ := by
  let := hD.condition
  let := hD.le
  exact ⟨fun v ↦ by simp [negate, DefinableForcingTower.ClassNegation]⟩

theorem close_defined (hD : D.Defines T) (F : V → V → Prop)
    (φ : SetTheorySemisentence 2) (hφ : ℒₛₑₜ-relation F via φ) :
    ℒₛₑₜ-relation (fun b ↦ T.ClassClosure (F b)) via D.close φ := by
  let := hD.condition
  let := hD.le
  exact ⟨fun v ↦ by simp [close, DefinableForcingTower.ClassClosure]⟩

/-- Compilation has the existing forcing semantics on all input assignments,
including assignments that are not tuples of names. No countability is used. -/
theorem compile_defined (hD : D.Defines T) {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation (T.towerFormula φ) via D.compile φ := by
  let := hD.condition
  let := hD.isName
  induction φ with
  | verum => exact ⟨fun v ↦ by simp [compile, DefinableForcingTower.towerFormula,
      DefinableForcingTower.towerFormulaData]⟩
  | falsum => exact ⟨fun v ↦ by simp [compile, DefinableForcingTower.towerFormula,
      DefinableForcingTower.towerFormulaData]⟩
  | rel r ts => exact atomic_defined hD r ts
  | nrel r ts => exact negate_defined hD _ _ (atomic_defined hD r ts)
  | and φ ψ ihφ ihψ =>
      exact ⟨fun v ↦ by simp [compile, DefinableForcingTower.towerFormula,
        DefinableForcingTower.towerFormulaData]⟩
  | or φ ψ ihφ ihψ =>
      apply close_defined hD
      exact ⟨fun v ↦ by simp [DefinableForcingTower.towerFormula]⟩
  | all φ ih =>
      exact ⟨fun v ↦ by simp [compile, DefinableForcingTower.towerFormula,
        DefinableForcingTower.towerFormulaData]⟩
  | exs φ ih =>
      apply close_defined hD
      exact ⟨fun v ↦ by simp [DefinableForcingTower.towerFormula]⟩

end ClassForcingFormulaDictionary
end ZFVP
