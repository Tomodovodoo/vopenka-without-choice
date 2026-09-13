import ZFVP.ModelTheory.ClassForcingTowerAtomicRegular
import ZFVP.ModelTheory.ClassForcingGenericAlgebra
import ZFVP.ModelTheory.ClassForcingQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

def towerAtomic {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (b p : V) : Prop :=
  match r with
  | .eq => T.ForcesEqual (forcingTermValue (ts 0) b) (forcingTermValue (ts 1) b) p
  | .mem => T.ForcesMember (forcingTermValue (ts 0) b) (forcingTermValue (ts 1) b) p

instance towerAtomic_definable {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) : ℒₛₑₜ-relation (T.towerAtomic r ts) := by
  cases r <;> unfold towerAtomic <;> definability

noncomputable def towerFormulaData (T : DefinableForcingTower V) :
    {n : ℕ} → SetTheorySemisentence n → {F : V → V → Prop // ℒₛₑₜ-relation F}
  | _, .verum => ⟨fun _ p ↦ T.Condition p, by definability⟩
  | _, .falsum => ⟨fun _ _ ↦ False, by definability⟩
  | _, .rel r ts => ⟨T.towerAtomic r ts, by definability⟩
  | _, .nrel r ts => ⟨fun b ↦ T.ClassNegation (T.towerAtomic r ts b), by
      unfold ClassNegation; definability⟩
  | _, .and φ ψ => by
      let f := T.towerFormulaData φ
      let g := T.towerFormulaData ψ
      have := f.property
      have := g.property
      exact ⟨fun b p ↦ f.val b p ∧ g.val b p, by definability⟩
  | _, .or φ ψ => by
      let f := T.towerFormulaData φ
      let g := T.towerFormulaData ψ
      have := f.property
      have := g.property
      exact ⟨fun b ↦ T.ClassClosure (fun p ↦ f.val b p ∨ g.val b p), by
        unfold ClassClosure; definability⟩
  | n, .all φ => by
      let f := T.towerFormulaData φ
      have := f.property
      exact ⟨fun b p ↦ T.Condition p ∧ ∀ x, T.IsName x →
        f.val (assignmentPrepend (n : V) b x) p, by definability⟩
  | n, .exs φ => by
      let f := T.towerFormulaData φ
      have := f.property
      exact ⟨fun b ↦ T.ClassClosure (fun p ↦ ∃ x, T.IsName x ∧
        f.val (assignmentPrepend (n : V) b x) p), by
          unfold ClassClosure; definability⟩

noncomputable def towerFormula {n : ℕ} (φ : SetTheorySemisentence n) : V → V → Prop :=
  (T.towerFormulaData φ).val

instance towerFormula_definable {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation (T.towerFormula φ) := (T.towerFormulaData φ).property

theorem towerAtomic_regular [Countable V] {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (v : Fin n → T.Name) :
    T.ClassRegular (T.towerAtomic r ts (standardTuple (fun i ↦ (v i).val))) := by
  cases r <;> unfold towerAtomic <;> dsimp only
  all_goals rw [ClassForcingQuotient.term_tuple T.IsName v (ts 0),
    ClassForcingQuotient.term_tuple T.IsName v (ts 1)]
  · exact T.forcesEqual_regular _ _
  · exact T.forcesMember_regular _ _

theorem towerFormula_regular [Countable V] {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → T.Name) :
    T.ClassRegular (T.towerFormula φ (standardTuple (fun i ↦ (v i).val))) := by
  induction φ with
  | verum => exact T.classRegular_top
  | falsum => exact T.classRegular_empty
  | rel r ts => exact T.towerAtomic_regular r ts v
  | nrel r ts => exact T.classNegation_regular _ (T.towerAtomic_regular r ts v).2.1
  | and φ ψ ihφ ihψ => exact T.classRegular_and (ihφ v) (ihψ v)
  | or φ ψ _ _ => exact T.classClosure_regular _
  | all φ ih =>
    apply T.classRegular_all
    intro x hx
    exact ih (⟨x, hx⟩ :> v)
  | exs φ _ => exact T.classClosure_regular _

end DefinableForcingTower
end ZFVP
