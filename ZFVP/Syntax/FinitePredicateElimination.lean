import ZFVP.SetTheory.FiniteDictionarySourceBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Formulas with a finite list of additional relation definitions. Pure
membership formulas include equality and graph-expanded defined terms. -/
inductive FinitePredicateFormula (D : SetFormulaDictionary) : ℕ → Type
  | pure {n} (φ : SetTheorySemisentence n) : FinitePredicateFormula D n
  | predicate {n} (i : Fin D.length) (args : Fin (D.get i).1 → Fin n) : FinitePredicateFormula D n
  | neg {n} (φ : FinitePredicateFormula D n) : FinitePredicateFormula D n
  | and {n} (φ ψ : FinitePredicateFormula D n) : FinitePredicateFormula D n
  | or {n} (φ ψ : FinitePredicateFormula D n) : FinitePredicateFormula D n
  | all {n} (φ : FinitePredicateFormula D (n + 1)) : FinitePredicateFormula D n
  | exs {n} (φ : FinitePredicateFormula D (n + 1)) : FinitePredicateFormula D n

namespace FinitePredicateFormula

/-- Structural predicate elimination. De Bruijn substitution preserves binders
and simultaneously replaces precisely the free variables of each definition. -/
def eliminate {D : SetFormulaDictionary} : {n : ℕ} → FinitePredicateFormula D n → SetTheorySemisentence n
  | _, .pure φ => φ
  | _, .predicate i args => (D.get i).2.subst (fun j ↦ Semiterm.bvar (args j))
  | _, .neg φ => ∼eliminate φ
  | _, .and φ ψ => eliminate φ ⋏ eliminate ψ
  | _, .or φ ψ => eliminate φ ⋎ eliminate ψ
  | _, .all φ => ∀' eliminate φ
  | _, .exs φ => ∃' eliminate φ

def evaluate {D : SetFormulaDictionary} {W : Type*} [SetStructure W] :
    {n : ℕ} → FinitePredicateFormula D n → (Fin n → W) → Prop
  | _, .pure φ, v => φ.Evalb v
  | _, .predicate i args, v => (D.get i).2.Evalb (fun j ↦ v (args j))
  | _, .neg φ, v => ¬evaluate φ v
  | _, .and φ ψ, v => evaluate φ v ∧ evaluate ψ v
  | _, .or φ ψ, v => evaluate φ v ∨ evaluate ψ v
  | _, .all φ, v => ∀ x, evaluate φ (x :> v)
  | _, .exs φ, v => ∃ x, evaluate φ (x :> v)

theorem eliminate_correct {D : SetFormulaDictionary} {n : ℕ} (φ : FinitePredicateFormula D n)
    {W : Type*} [SetStructure W] (v : Fin n → W) :
    φ.eliminate.Evalb v ↔ φ.evaluate v := by
  induction φ with
  | pure φ => rfl
  | predicate i args =>
    simp [eliminate, evaluate, Semiformula.Evalb, Semiformula.eval_substs, Function.comp_def]
  | neg φ ih => simpa [eliminate, evaluate] using not_congr (ih v)
  | and φ ψ ihφ ihψ => simpa [eliminate, evaluate] using and_congr (ihφ v) (ihψ v)
  | or φ ψ ihφ ihψ => simpa [eliminate, evaluate] using or_congr (ihφ v) (ihψ v)
  | all φ ih => simpa [eliminate, evaluate] using forall_congr' (fun x ↦ ih (x :> v))
  | exs φ ih => simpa [eliminate, evaluate] using exists_congr (fun x ↦ ih (x :> v))

def eliminateList {D : SetFormulaDictionary} (Σ : List (FinitePredicateFormula D 6)) :
    List (SetTheorySemisentence 6) := Σ.map eliminate

theorem eliminateList_correct {D : SetFormulaDictionary} (Σ : List (FinitePredicateFormula D 6))
    {W : Type*} [SetStructure W] (v : Fin 6 → W) :
    (∀ e ∈ eliminateList Σ, e.Evalb v) ↔ ∀ e ∈ Σ, e.evaluate v := by
  simp only [eliminateList, List.forall_mem_map, eliminate_correct]

end FinitePredicateFormula
end ZFVP
