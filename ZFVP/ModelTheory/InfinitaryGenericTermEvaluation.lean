import ZFVP.ModelTheory.InfinitaryGenericStructure

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.CoordinateTerm

/-- Evaluate a first-order term using coordinate terms for its variables. -/
def evalTerm {L : Language} {n} : Semiterm L Empty n →
    (Fin n → CoordinateTerm L) → CoordinateTerm L
  | .bvar i, ts => ts i
  | .fvar i, _ => nomatch i
  | .func f v, ts => func f (fun i ↦ evalTerm (v i) ts)

theorem evalTerm_arity_le {L : Language} {n N} (t : Semiterm L Empty n)
    (ts : Fin n → CoordinateTerm L) (h : ∀ i, (ts i).1 ≤ N) :
    (evalTerm t ts).1 ≤ N := by
  induction t with
  | bvar i => exact h i
  | fvar i => exact i.elim
  | func f v ih => exact arity_le ih

theorem val_evalTerm {L : Language} {M : Type*} [s : Structure L M] {n N}
    (t : Semiterm L Empty n) (ts : Fin n → CoordinateTerm L)
    (h : ∀ i, (ts i).1 ≤ N) (b : Fin N → M) :
    (evalTerm t ts).2.val (b ∘ Formula.rightEmbed (evalTerm_arity_le t ts h)) Empty.elim =
      t.val (fun i ↦ (ts i).2.val (b ∘ Formula.rightEmbed (h i)) Empty.elim) Empty.elim := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f v ih =>
    change (func f (fun i ↦ evalTerm (v i) ts)).2.val _ _ = s.func f _
    apply Eq.trans (val_func_at f (fun i ↦ evalTerm (v i) ts) _ b)
    congr 1
    funext i
    exact ih i

end HenkinConstruction.FragmentExtension.CoordinateTerm
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem term_val {n} (t : Semiterm (limit L) Empty n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    t.val (s := C.extensionStructure) (fun i ↦ C.termClass (ts i)) Empty.elim =
      C.termClass (CoordinateTerm.evalTerm t ts) := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f v ih =>
    change Structure.func f (fun i ↦ (v i).val _ _) = _
    rw [funext ih]
    exact C.func_termClass f _

/-- Substitution agrees with evaluation of the substituted coordinate terms. -/
theorem eval_subst_iff {n m} (φ : Formula (limit L) n)
    (σ : Fin n → Semiterm (limit L) Empty m) (ts : Fin m → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.subst σ) ts ↔
      CoordinateTerm.Eval C.point φ (fun i ↦ CoordinateTerm.evalTerm (σ i) ts) := by
  constructor
  · rintro ⟨k, hs, hh⟩
    refine ⟨k, fun i ↦ CoordinateTerm.evalTerm_arity_le (σ i) ts hs, ?_⟩
    intro b hb
    have hv := (Formula.weakEval_subst H.weakQuantifier σ φ _).mp (hh b hb)
    have ht : (fun i ↦ (CoordinateTerm.evalTerm (σ i) ts).2.val
        (b ∘ Formula.rightEmbed (CoordinateTerm.evalTerm_arity_le (σ i) ts hs)) Empty.elim) =
        (fun i ↦ (σ i).val
          (fun j ↦ (ts j).2.val (b ∘ Formula.rightEmbed (hs j)) Empty.elim) Empty.elim) :=
      funext fun i ↦ CoordinateTerm.val_evalTerm (σ i) ts hs b
    exact ht ▸ hv
  · rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := C.coordinate_cofinal (CoordinateTerm.arity ts)
    have hg := (C.refines (Nat.le_max_right k j)).choose
    have h : CoordinateTerm.arity ts ≤ 1 + (C.point (max k j)).1 := by omega
    let hs := fun i ↦ (CoordinateTerm.le_arity ts i).trans h
    obtain ⟨ht, hh⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_left k j)) hk
    refine ⟨max k j, hs, ?_⟩
    intro b hb
    apply (Formula.weakEval_subst H.weakQuantifier σ φ _).mpr
    have hv : (fun i ↦ (CoordinateTerm.evalTerm (σ i) ts).2.val
        (b ∘ Formula.rightEmbed (ht i)) Empty.elim) =
        (fun i ↦ (σ i).val
          (fun j ↦ (ts j).2.val (b ∘ Formula.rightEmbed (hs j)) Empty.elim) Empty.elim) := by
      funext i
      exact CoordinateTerm.val_evalTerm (σ i) ts hs b
    exact hv ▸ hh b hb

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
