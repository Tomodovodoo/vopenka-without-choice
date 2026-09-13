import ZFVP.ModelTheory.InfinitaryCoordinateTermRelation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.CoordinateTerm
open HenkinLanguage FragmentClosure FiniteCondition

/-- A common arity for a finite tuple of coordinate terms. -/
def arity {L : Language} {k} (v : Fin k → CoordinateTerm L) : ℕ :=
  Finset.univ.sup fun i ↦ (v i).1

theorem le_arity {L : Language} {k} (v : Fin k → CoordinateTerm L) (i : Fin k) :
    (v i).1 ≤ arity v := by
  exact Finset.le_sup (f := fun i ↦ (v i).1) (Finset.mem_univ i)

theorem arity_le {L : Language} {k N} {v : Fin k → CoordinateTerm L}
    (h : ∀ i, (v i).1 ≤ N) : arity v ≤ N :=
  Finset.sup_le fun i _ ↦ h i

/-- Apply a function symbol after lifting its argument terms to a common arity. -/
def func {L : Language} {k} (f : L.Func k) (v : Fin k → CoordinateTerm L) : CoordinateTerm L :=
  ⟨arity v, .func f (fun i ↦ Formula.liftRightTerm (le_arity v i) (v i).2)⟩

@[simp] theorem val_func {L : Language} {M : Type*} [s : Structure L M] {k}
    (f : L.Func k) (v : Fin k → CoordinateTerm L) (b : Fin (arity v) → M) :
    (func f v).2.val b Empty.elim =
      s.func f (fun i ↦ (v i).2.val (b ∘ Formula.rightEmbed (le_arity v i)) Empty.elim) := by
  simp only [func, Semiterm.val_func, Function.comp_def, Formula.val_liftRightTerm]

theorem val_func_at {L : Language} {M : Type*} [s : Structure L M] {k N}
    (f : L.Func k) (v : Fin k → CoordinateTerm L) (h : arity v ≤ N) (b : Fin N → M) :
    (func f v).2.val (b ∘ Formula.rightEmbed h) Empty.elim =
      s.func f (fun i ↦ (v i).2.val
        (b ∘ Formula.rightEmbed ((le_arity v i).trans h)) Empty.elim) := by
  simp only [val_func, Function.comp_def, Formula.rightEmbed_trans]

variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

theorem equalAt_func {p : H.FiniteCondition} {k} (f : (limit L).Func k)
    {v w : Fin k → CoordinateTerm (limit L)} (he : ∀ i, EqualAt p (v i) (w i)) :
    EqualAt p (func f v) (func f w) := by
  have hv : arity v ≤ 1 + p.1 := arity_le fun i ↦ (he i).choose
  have hw : arity w ≤ 1 + p.1 := arity_le fun i ↦ (he i).choose_spec.choose
  refine ⟨hv, hw, ?_⟩
  intro b hb
  apply Eq.trans (val_func_at f v hv b)
  apply Eq.trans ?_ (val_func_at f w hw b).symm
  congr 1
  funext i
  exact (he i).choose_spec.choose_spec b hb

variable (c : ℕ → H.FiniteCondition)
  (hc : ∀ {i j}, i ≤ j → Refines (c i) (c j))
  (ha : ∀ n, ∃ i, n ≤ 1 + (c i).1)

include hc in
theorem rel_func {k} (f : (limit L).Func k) {v w : Fin k → CoordinateTerm (limit L)}
    (he : ∀ i, Rel c (v i) (w i)) : Rel c (func f v) (func f w) := by
  classical
  choose j hj using he
  let m := Finset.univ.sup j
  refine ⟨m, equalAt_func f (fun i ↦ ?_)⟩
  exact equalAt_persistent (hc (Finset.le_sup (Finset.mem_univ i))) (hj i)

/-- The coordinate-term function operation descends to the equality quotient. -/
noncomputable def quotientFunc {k} (f : (limit L).Func k)
    (v : Fin k → Quotient (setoid c hc ha)) : Quotient (setoid c hc ha) :=
  Quotient.mk _ (func f (fun i ↦ (v i).out))

@[simp] theorem quotientFunc_mk {k} (f : (limit L).Func k)
    (v : Fin k → CoordinateTerm (limit L)) :
    quotientFunc c hc ha f (fun i ↦ Quotient.mk (setoid c hc ha) (v i)) =
      Quotient.mk (setoid c hc ha) (func f v) := by
  apply Quotient.sound
  apply rel_func c hc
  intro i
  exact Quotient.exact (Quotient.out_eq (Quotient.mk (setoid c hc ha) (v i)))

end HenkinConstruction.FragmentExtension.CoordinateTerm
end ZFVP.Infinitary
