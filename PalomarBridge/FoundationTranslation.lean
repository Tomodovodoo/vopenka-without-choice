import PalomarBridge.Vocabulary
import Foundation.FirstOrder.SetTheory.Basic.Misc
import Mathlib.Tactic.FinCases

/-! Translation of the independent membership syntax into Foundation syntax.
This module is proof-side material and is not an allowed Challenge import. -/

namespace PalomarBridge
open LO LO.FirstOrder

/-- Translation into the exact membership language used by the main proof. -/
def Formula.toFoundation : {n : Nat} → Formula n → SetTheorySemisentence n
  | _, .truth => .verum
  | _, .falsity => .falsum
  | _, .equal i j => .rel .eq ![.bvar i, .bvar j]
  | _, .unequal i j => .nrel .eq ![.bvar i, .bvar j]
  | _, .member i j => .rel .mem ![.bvar i, .bvar j]
  | _, .nonmember i j => .nrel .mem ![.bvar i, .bvar j]
  | _, .conj p q => .and p.toFoundation q.toFoundation
  | _, .disj p q => .or p.toFoundation q.toFoundation
  | _, .all p => .all p.toFoundation
  | _, .exists_ p => .exs p.toFoundation

/-- Every term in this function-free language with no free parameters is a
bound variable. -/
def variableIndex : SetTheorySemiterm Empty n → Fin n
  | .bvar i => i
  | .fvar e => Empty.elim e
  | .func e _ => Empty.elim e

/-- Inverse syntax translation. Both equality and membership remain explicit. -/
def fromFoundation : {n : Nat} → SetTheorySemisentence n → Formula n
  | _, .verum => .truth
  | _, .falsum => .falsity
  | _, .rel .eq v => .equal (variableIndex (v 0)) (variableIndex (v 1))
  | _, .nrel .eq v => .unequal (variableIndex (v 0)) (variableIndex (v 1))
  | _, .rel .mem v => .member (variableIndex (v 0)) (variableIndex (v 1))
  | _, .nrel .mem v => .nonmember (variableIndex (v 0)) (variableIndex (v 1))
  | _, .and p q => .conj (fromFoundation p) (fromFoundation q)
  | _, .or p q => .disj (fromFoundation p) (fromFoundation q)
  | _, .all p => .all (fromFoundation p)
  | _, .exs p => .exists_ (fromFoundation p)

@[simp] theorem fromFoundation_toFoundation (p : Formula n) :
    fromFoundation p.toFoundation = p := by
  induction p <;> simp_all [Formula.toFoundation, fromFoundation, variableIndex]

@[simp] theorem bvar_variableIndex (t : SetTheorySemiterm Empty n) :
    Semiterm.bvar (variableIndex t) = t := by
  cases t with
  | bvar i => rfl
  | fvar e => exact Empty.elim e
  | func e _ => exact Empty.elim e

@[simp] theorem toFoundation_fromFoundation (p : SetTheorySemisentence n) :
    (fromFoundation p).toFoundation = p := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r <;> simp only [fromFoundation, Formula.toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | nrel r v =>
    cases r <;> simp only [fromFoundation, Formula.toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | and p q hp hq => simp [fromFoundation, Formula.toFoundation, hp, hq]
  | or p q hp hq => simp [fromFoundation, Formula.toFoundation, hp, hq]
  | all p hp => simp [fromFoundation, Formula.toFoundation, hp]
  | exs p hp => simp [fromFoundation, Formula.toFoundation, hp]

/-- Translation preserves truth in every membership structure, without a ZF,
well-foundedness, or countability assumption. -/
theorem realize_toFoundation {M : Type u} [SetStructure M]
    (p : Formula n) (v : Fin n → M) :
    p.toFoundation.Evalb v ↔ p.Realize (fun x y : M => x ∈ y) v := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal i j => rfl
  | unequal i j => rfl
  | member i j => rfl
  | nonmember i j => rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | disj p q hp hq => exact or_congr (hp v) (hq v)
  | all p hp => exact forall_congr' (fun x => hp (v := Fin.cons x v))
  | exists_ p hp => exact exists_congr (fun x => hp (v := Fin.cons x v))

/-- The independent theory obtained by translating every source sentence.
This definition belongs to the Solution side. A submission must independently
define the particular theories in its Challenge and prove their identification. -/
def translateTheory (T : LO.FirstOrder.SetTheory) : Theory := fromFoundation '' T

/-- The syntax conversion preserves and reflects all axioms of a theory. -/
theorem models_translateTheory_iff {M : Type u} [SetStructure M] [Nonempty M]
    (T : LO.FirstOrder.SetTheory) :
    Models (fun x y : M => x ∈ y) (translateTheory T) ↔ M↓[ℒₛₑₜ] ⊧* T := by
  have hv : (Fin.elim0 : Fin 0 → M) = ![] := Subsingleton.elim _ _
  constructor
  · rintro ⟨_, h⟩
    constructor
    intro p hp
    have ht := h (fromFoundation p) ⟨p, hp, rfl⟩
    have hs := (realize_toFoundation (fromFoundation p) (Fin.elim0 : Fin 0 → M)).mpr ht
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb, hv] using hs
  · intro h
    refine ⟨inferInstance, ?_⟩
    rintro p ⟨q, hq, rfl⟩
    apply (realize_toFoundation (fromFoundation q) (Fin.elim0 : Fin 0 → M)).mp
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb, hv] using LO.FirstOrder.Theory.models M T hq

/-- Completeness and equality normalization give the exact connection between
semantic consistency in the independent syntax and Foundation consistency.
The explicit premise only requests Foundation's usual equality axioms. -/
theorem satisfiable_translateTheory_iff (T : LO.FirstOrder.SetTheory)
    (hEq : (𝗘𝗤 ℒₛₑₜ : LO.FirstOrder.SetTheory) ⊆ T) :
    Satisfiable (translateTheory T) ↔ LO.Entailment.Consistent T := by
  constructor
  · rintro ⟨M, mem, hM⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hM.1
    have hm : M↓[ℒₛₑₜ] ⊧* T := (models_translateTheory_iff T).mp hM
    exact LO.FirstOrder.Theory.consistent_of_satisfiable ⟨M↓[ℒₛₑₜ], hm⟩
  · intro h
    obtain ⟨M, hne, hstr, hM⟩ :=
      LO.FirstOrder.satisfiable_iff.mp (LO.FirstOrder.Theory.small_satisfiable_of_consistent h)
    let := hne
    let := hstr
    let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun p hp => hM.models_set (hEq hp)⟩
    let N := LO.FirstOrder.SetTheory.QuotNormalize M
    have hN : N↓[ℒₛₑₜ] ⊧* T := (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
    exact ⟨N, (fun x y : N => x ∈ y), (models_translateTheory_iff T).mpr hN⟩

end PalomarBridge







