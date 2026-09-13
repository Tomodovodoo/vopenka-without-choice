import ZFVP.ModelTheory.InfinitarySmallTermFreezing
import ZFVP.ModelTheory.InfinitaryParameterInstance

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace Adequate

theorem finite_union (hM : M.Adequate S) {n} (φ ψ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hψ : ⟨n + 1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) :
    M.Q {x | Formula.WeakEval M.Q φ (x :> b) ∨ Formula.WeakEval M.Q ψ (x :> b)} →
      M.Q {x | Formula.WeakEval M.Q φ (x :> b)} ∨
      M.Q {x | Formula.WeakEval M.Q ψ (x :> b)} := by
  simpa only [Formula.qFiniteUnion, Formula.weakEval_imp, Formula.weakEval_q,
    Formula.weakEval_or] using hM.finiteUnion φ ψ hφ hψ b

/-- The represented countable-union law survives finite old parameter naming. -/
theorem parameter_countable_union (hM : M.Adequate S) {n}
    (s : ParameterSequence M S (n + 1)) (a : Fin n → M.Domain) :
    M.Q {x | ∃ i, (s.component i).Eval (x :> a)} →
      ∃ i, M.Q {x | (s.component i).Eval (x :> a)} := by
  let ρ := Fin.cast (show n + 1 + s.1 = n + s.1 + 1 by omega)
  have hf := FragmentClosure.rename_closed s.2.1.2 ρ
  have hh := hM.countableUnion (fun i ↦ (s.2.1.1 i).rename ρ) hf (Fin.append a s.2.2)
  simpa only [Formula.qCountableUnion, Formula.weakEval_imp, Formula.disj, Formula.weakEval_neg, Formula.weakEval_conj, not_forall, not_not,
    Formula.weakEval_q, Formula.weakEval_rename, ρ, ParameterInstance.cons_append,
    ParameterInstance.Eval, ParameterSequence.component] using hh


/-- The two fibers may use different finite lists of old names. -/
theorem parameter_finite_union (hM : M.Adequate S) {n}
    (p q : ParameterInstance M S (n + 1)) (a : Fin n → M.Domain) :
    M.Q {x | p.Eval (x :> a) ∨ q.Eval (x :> a)} →
      M.Q {x | p.Eval (x :> a)} ∨ M.Q {x | q.Eval (x :> a)} := by
  let k := p.1 + q.1
  let ρ : Fin (n + 1 + p.1) → Fin (n + 1 + k) :=
    Fin.addCases (Fin.castAdd k) (fun i ↦ Fin.natAdd (n + 1) (Fin.castAdd q.1 i))
  let σ : Fin (n + 1 + q.1) → Fin (n + 1 + k) :=
    Fin.addCases (Fin.castAdd k) (fun i ↦ Fin.natAdd (n + 1) (Fin.natAdd p.1 i))
  let c := Fin.cast (show n + 1 + k = n + k + 1 by omega)
  let φ := (p.2.1.1.rename ρ).rename c
  let ψ := (q.2.1.1.rename σ).rename c
  have hφ := FragmentClosure.rename_closed (FragmentClosure.rename_closed p.2.1.2 ρ) c
  have hψ := FragmentClosure.rename_closed (FragmentClosure.rename_closed q.2.1.2 σ) c
  let b := Fin.append p.2.2 q.2.2
  have hp (x : M.Domain) : Formula.WeakEval M.Q φ (x :> Fin.append a b) ↔ p.Eval (x :> a) := by
    simp only [φ, Formula.weakEval_rename, c, ParameterInstance.cons_append]
    apply Iff.of_eq
    unfold ParameterInstance.Eval
    congr 1
    funext i
    cases i using Fin.addCases <;> simp [Function.comp_def, ρ, b, k]
  have hq (x : M.Domain) : Formula.WeakEval M.Q ψ (x :> Fin.append a b) ↔ q.Eval (x :> a) := by
    simp only [ψ, Formula.weakEval_rename, c, ParameterInstance.cons_append]
    apply Iff.of_eq
    unfold ParameterInstance.Eval
    congr 1
    funext i
    cases i using Fin.addCases <;> simp [Function.comp_def, σ, b, k]
  simpa only [hp, hq] using hM.finite_union φ ψ hφ hψ (Fin.append a b)


omit [L.Encodable] in
private theorem cons_cons_append {n k} (x y : M.Domain) (a : Fin n → M.Domain)
    (b : Fin k → M.Domain) :
    (x :> y :> Fin.append a b) ∘ Fin.cast (show n + 1 + 1 + k = n + k + 1 + 1 by omega) =
      Fin.append (x :> y :> a) b := by
  have h : Matrix.vecAppend (show n + k + 1 + 1 = n + 1 + 1 + k by omega)
      (Matrix.vecCons x (Matrix.vecCons y a)) b =
      Matrix.vecCons x (Matrix.vecCons y (Fin.append a b)) := by
    rw [Matrix.cons_vecAppend, Matrix.cons_vecAppend]
    rfl
  dsimp [Matrix.vecAppend] at h
  have h' := congrArg (fun f ↦ f ∘ Fin.cast (show n + 1 + 1 + k = n + k + 1 + 1 by omega)) h
  simpa [Function.comp_def, Matrix.vecCons, Fin.cast_cast] using h'.symm

/-- Interchange applies to a named matrix at every finite assignment. -/
theorem parameter_interchange (hM : M.Adequate S) {n}
    (p : ParameterInstance M S (n + 1 + 1)) (a : Fin n → M.Domain) :
    M.Q {y | ∃ x, p.Eval (x :> y :> a)} →
      (∃ x, M.Q {y | p.Eval (x :> y :> a)}) ∨ M.Q {x | ∃ y, p.Eval (x :> y :> a)} := by
  let ρ := Fin.cast (show n + 1 + 1 + p.1 = n + p.1 + 1 + 1 by omega)
  have hf := FragmentClosure.rename_closed p.2.1.2 ρ
  have hh := hM.interchange (p.2.1.1.rename ρ) hf (Fin.append a p.2.2)
  simpa only [Formula.qInterchange, Formula.weakEval_imp, Formula.weakEval_or,
    Formula.weakEval_q, Formula.weakEval_exs, Formula.weakEval_swapFirstTwo,
    Formula.weakEval_rename, ρ, cons_cons_append, ParameterInstance.Eval] using hh

/-- A small witness projection forces an old witness with a large remaining fiber. -/
theorem parameter_large_witness (hM : M.Adequate S) {n}
    (p : ParameterInstance M S (n + 1 + 1)) (a : Fin n → M.Domain)
    (hq : M.Q {y | ∃ x, p.Eval (x :> y :> a)})
    (hs : ¬M.Q {x | ∃ y, p.Eval (x :> y :> a)}) :
    ∃ x, M.Q {y | p.Eval (x :> y :> a)} :=
  (hM.parameter_interchange p a hq).resolve_right hs

end Adequate
end WeakModel
end ZFVP.Infinitary

