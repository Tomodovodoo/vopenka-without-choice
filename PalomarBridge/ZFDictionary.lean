import PalomarBridge.FoundationTranslation
import Foundation.FirstOrder.SetTheory.Basic.Axioms

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def openTerm : (Fin n ⊕ Nat) → SetTheorySemiterm Nat n
  | .inl i => .bvar i
  | .inr i => .fvar i

def OpenFormula.toFoundation : {n : Nat} → OpenFormula n → SetTheorySemiproposition n
  | _, .truth => .verum
  | _, .falsity => .falsum
  | _, .equal i j => .rel .eq ![openTerm i, openTerm j]
  | _, .unequal i j => .nrel .eq ![openTerm i, openTerm j]
  | _, .member i j => .rel .mem ![openTerm i, openTerm j]
  | _, .nonmember i j => .nrel .mem ![openTerm i, openTerm j]
  | _, .conj p q => .and p.toFoundation q.toFoundation
  | _, .disj p q => .or p.toFoundation q.toFoundation
  | _, .all p => .all p.toFoundation
  | _, .exists_ p => .exs p.toFoundation

def openVariable : SetTheorySemiterm Nat n → Fin n ⊕ Nat
  | .bvar i => .inl i
  | .fvar i => .inr i
  | .func e _ => Empty.elim e

def openFromFoundation : {n : Nat} → SetTheorySemiproposition n → OpenFormula n
  | _, .verum => .truth
  | _, .falsum => .falsity
  | _, .rel .eq v => .equal (openVariable (v 0)) (openVariable (v 1))
  | _, .nrel .eq v => .unequal (openVariable (v 0)) (openVariable (v 1))
  | _, .rel .mem v => .member (openVariable (v 0)) (openVariable (v 1))
  | _, .nrel .mem v => .nonmember (openVariable (v 0)) (openVariable (v 1))
  | _, .and p q => .conj (openFromFoundation p) (openFromFoundation q)
  | _, .or p q => .disj (openFromFoundation p) (openFromFoundation q)
  | _, .all p => .all (openFromFoundation p)
  | _, .exs p => .exists_ (openFromFoundation p)

@[simp] theorem openTerm_openVariable (t : SetTheorySemiterm Nat n) :
    openTerm (openVariable t) = t := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func e _ => exact Empty.elim e

@[simp] theorem openToFoundation_fromFoundation (p : SetTheorySemiproposition n) :
    (openFromFoundation p).toFoundation = p := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r <;> simp only [openFromFoundation, OpenFormula.toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | nrel r v =>
    cases r <;> simp only [openFromFoundation, OpenFormula.toFoundation]
    all_goals congr 1; funext i; fin_cases i <;> simp
  | and p q hp hq => simp [openFromFoundation, OpenFormula.toFoundation, hp, hq]
  | or p q hp hq => simp [openFromFoundation, OpenFormula.toFoundation, hp, hq]
  | all p hp => simp [openFromFoundation, OpenFormula.toFoundation, hp]
  | exs p hp => simp [openFromFoundation, OpenFormula.toFoundation, hp]

@[simp] theorem openTerm_val {M : Type u} [SetStructure M]
    (i : Fin n ⊕ Nat) (a : Nat → M) (v : Fin n → M) :
    (openTerm i).val v a = Sum.elim v a i := by cases i <;> rfl

theorem realize_openToFoundation {M : Type u} [SetStructure M]
    (p : OpenFormula n) (a : Nat → M) (v : Fin n → M) :
    p.toFoundation.Eval v a ↔ p.Realize (fun x y : M => x ∈ y) a v := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal i j => cases i <;> cases j <;> rfl
  | unequal i j => cases i <;> cases j <;> rfl
  | member i j => cases i <;> cases j <;> rfl
  | nonmember i j => cases i <;> cases j <;> rfl
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | disj p q hp hq => exact or_congr (hp v) (hq v)
  | all p hp => exact forall_congr' (fun x => hp (v := Fin.cons x v))
  | exists_ p hp => exact exists_congr (fun x => hp (v := Fin.cons x v))

variable {M : Type u} [SetStructure M] [Nonempty M]

/-- The independent schema includes all parameter instances of separation. -/
theorem eval_separationSchema (p : OpenFormula 1) :
    M↓[ℒₛₑₜ] ⊧ Axiom.separationSchema p.toFoundation ↔
    ∀ (a : Nat → M) (x : M), ∃ y : M, ∀ z : M, z ∈ y ↔ z ∈ x ∧
      p.Realize (fun x y : M => x ∈ y) a ![z] := by
  simp [Axiom.separationSchema, models_iff_proposition, realize_openToFoundation]

/-- The independent schema includes all parameter instances of replacement. -/
theorem eval_replacementSchema (p : OpenFormula 2) :
    M↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema p.toFoundation ↔
    ∀ (a : Nat → M), (∀ x, ∃! y, p.Realize (fun x y : M => x ∈ y) a ![x, y]) →
      ∀ X : M, ∃ Y : M, ∀ y : M, y ∈ Y ↔ ∃ x, x ∈ X ∧
        p.Realize (fun x y : M => x ∈ y) a ![x, y] := by
  simp [Axiom.replacementSchema, models_iff_proposition, realize_openToFoundation, ExistsUnique]

/-- The independent ZF definition is equivalent to the entire Foundation ZF
axiom set, including every separation and replacement instance. -/
theorem isZF_iff_models :
    IsZF (fun x y : M => x ∈ y) ↔ M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  · intro h
    constructor
    intro p hp
    cases hp with
    | axiom_of_equality p hp => exact Theory.models M (𝗘𝗤 ℒₛₑₜ) hp
    | axiom_of_empty_set =>
      simpa [models_iff, Semiformula.Realize, Axiom.empty] using h.empty
    | axiom_of_extentionality =>
      simpa [models_iff, Semiformula.Realize, Axiom.extentionality] using h.extensionality
    | axiom_of_pairing =>
      simpa [models_iff, Semiformula.Realize, Axiom.pairing] using h.pairing
    | axiom_of_union =>
      simpa [models_iff, Semiformula.Realize, Axiom.union] using h.union
    | axiom_of_power_set =>
      simpa [models_iff, Semiformula.Realize, Axiom.power, isSubsetOf] using h.power
    | axiom_of_infinity =>
      simpa [models_iff, Semiformula.Realize, Axiom.infinity, isEmpty, isSucc, Rew.q, Rew.subst] using h.infinity
    | axiom_of_foundation =>
      simpa [models_iff, Semiformula.Realize, Axiom.foundation, isNonempty, Rew.q, Rew.subst] using h.foundation
    | axiom_of_separation p =>
      simpa using (eval_separationSchema (openFromFoundation p)).mpr
        (h.separation (openFromFoundation p))
    | axiom_of_replacement p =>
      simpa using (eval_replacementSchema (openFromFoundation p)).mpr
        (h.replacement (openFromFoundation p))
  · intro h
    have ax (p : SetTheorySentence) (hp : p ∈ 𝗭𝗙) := h.models_set hp
    refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [models_iff, Semiformula.Realize, Axiom.empty] using
        ax Axiom.empty ZermeloFraenkel.axiom_of_empty_set
    · simpa [models_iff, Semiformula.Realize, Axiom.extentionality] using
        ax Axiom.extentionality ZermeloFraenkel.axiom_of_extentionality
    · simpa [models_iff, Semiformula.Realize, Axiom.pairing] using
        ax Axiom.pairing ZermeloFraenkel.axiom_of_pairing
    · simpa [models_iff, Semiformula.Realize, Axiom.union] using
        ax Axiom.union ZermeloFraenkel.axiom_of_union
    · simpa [models_iff, Semiformula.Realize, Axiom.power, isSubsetOf] using
        ax Axiom.power ZermeloFraenkel.axiom_of_power_set
    · simpa [models_iff, Semiformula.Realize, Axiom.infinity, isEmpty, isSucc, Rew.q, Rew.subst] using
        ax Axiom.infinity ZermeloFraenkel.axiom_of_infinity
    · simpa [models_iff, Semiformula.Realize, Axiom.foundation, isNonempty, Rew.q, Rew.subst] using
        ax Axiom.foundation ZermeloFraenkel.axiom_of_foundation
    · intro p
      exact (eval_separationSchema p).mp
        (ax _ (ZermeloFraenkel.axiom_of_separation p.toFoundation))
    · intro p
      exact (eval_replacementSchema p).mp
        (ax _ (ZermeloFraenkel.axiom_of_replacement p.toFoundation))

/-- The independent choice definition is exactly the imported choice axiom. -/
theorem hasChoice_iff_models :
    HasChoice (fun x y : M => x ∈ y) ↔ M↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  simp [HasChoice, AxiomOfChoice, models_iff, Semiformula.Realize, Axiom.choice,
    isNonempty, ExistsUnique, Rew.q, Rew.subst]

end PalomarBridge






