import ZFVP.ModelTheory.InfinitaryAdequateOldEmbedding
import Mathlib.Tactic.FinCases

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace ParameterInstance

def ofFirstOrder {n} (φ : Semisentence L n) : ParameterInstance M S n :=
  ofFormula (.fo φ) (FragmentClosure.fo_closed φ)

@[simp] theorem eval_ofFirstOrder {n} (φ : Semisentence L n) (b : Fin n → M.Domain) :
    (ofFirstOrder (S := S) φ).Eval b ↔ φ.Evalb b := by
  exact eval_ofFormula _ _ _

def termGraph {n} (t : Semiterm L Empty n) : ParameterInstance M S (n + 1) :=
  ofFirstOrder (.rel Language.Eq.eq ![.bvar 0, Rew.bShift t])

@[simp] theorem eval_termGraph {n} (t : Semiterm L Empty n) (x : M.Domain)
    (b : Fin n → M.Domain) : (termGraph (S := S) t).Eval (x :> b) ↔ x = t.val b Empty.elim := by
  simp [termGraph, Semiformula.eval_rel]

def atom {n} (r : L.Rel n) : ParameterInstance M S n :=
  ofFirstOrder (.rel r (fun i ↦ .bvar i))

@[simp] theorem eval_atom {n} (r : L.Rel n) (b : Fin n → M.Domain) :
    (atom (S := S) r).Eval b ↔ Structure.rel r b := by
  simp [atom, Semiformula.eval_rel, Function.comp_def]

end ParameterInstance

namespace AdequateGenericChain
open AdequateFiniteCondition
variable {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

def TermValueAt (p : AdequateFiniteCondition M S) {n} (t : Semiterm L Empty n)
    (ts : Fin n → ℕ) (r : ℕ) : Prop :=
  ∃ hr : r < 1 + p.1, ∃ ht : ∀ i, ts i < 1 + p.1,
    ∀ b, p.2.formula.Eval b → b (RightCoordinate.index hr) =
      t.val (fun i ↦ b (RightCoordinate.index (ht i))) Empty.elim

def TermValue {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) (r : ℕ) : Prop :=
  ∃ k, TermValueAt (C.point k) t ts r

theorem termValue_iff {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) (r : ℕ) :
    C.TermValue t ts r ↔ C.Eval (ParameterInstance.termGraph t) (r :> ts) := by
  constructor
  · rintro ⟨k, hr, ht, hh⟩
    have hfit : ∀ i, (r :> ts) i < 1 + (C.point k).1 := Fin.cases hr ht
    refine ⟨k, hfit, ?_⟩
    intro b hb
    have he : (fun i ↦ b (RightCoordinate.index (hfit i))) =
        b (RightCoordinate.index hr) :> fun i ↦ b (RightCoordinate.index (ht i)) := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [he, ParameterInstance.eval_termGraph]
    exact hh b hb
  · rintro ⟨k, ht, hh⟩
    refine ⟨k, ht 0, fun i ↦ ht i.succ, ?_⟩
    intro b hb
    have he : (fun i ↦ b (RightCoordinate.index (ht i))) =
        b (RightCoordinate.index (ht 0)) :> fun i ↦ b (RightCoordinate.index (ht i.succ)) := by
      funext i
      cases i using Fin.cases <;> rfl
    have h := hh b hb
    rw [he, ParameterInstance.eval_termGraph] at h
    exact h

theorem termValueAt_persistent {p q : AdequateFiniteCondition M S} (hpq : Refines p q)
    {n} {t : Semiterm L Empty n} {ts r} (hv : TermValueAt p t ts r) : TermValueAt q t ts r := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨hr, ht, hh⟩ := hv
  refine ⟨hr.trans_le (Nat.add_le_add_left g 1),
    fun i ↦ (ht i).trans_le (Nat.add_le_add_left g 1), ?_⟩
  intro b hb
  have h := hh _ (hg b hb)
  simpa only [Function.comp_apply, RightCoordinate.embed_index] using h

theorem exists_termValue {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) :
    ∃ r, C.TermValue t ts r := by
  have h : C.Eval (ParameterInstance.termGraph t).exs ts := C.eval_of_valid _ _ (by
    intro b
    apply (ParameterInstance.eval_exs _ _).mpr
    exact ⟨t.val b Empty.elim, (ParameterInstance.eval_termGraph _ _ _).mpr rfl⟩)
  obtain ⟨r, hr⟩ := (C.eval_exs _ _).mp h
  exact ⟨r, (C.termValue_iff t ts r).mpr hr⟩

noncomputable def termCoordinate {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) : ℕ :=
  (C.exists_termValue t ts).choose

theorem termCoordinate_value {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) :
    C.TermValue t ts (C.termCoordinate t ts) := (C.exists_termValue t ts).choose_spec

theorem termValue_unique {n} {t : Semiterm L Empty n} {ts r s}
    (hr : C.TermValue t ts r) (hs : C.TermValue t ts s) : C.Equal r s := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨l, hl⟩ := hs
  obtain ⟨hr, ht, hh⟩ := termValueAt_persistent (C.refines (Nat.le_max_left k l)) hk
  obtain ⟨hs, hu, hg⟩ := termValueAt_persistent (C.refines (Nat.le_max_right k l)) hl
  exact ⟨max k l, hr, hs, fun b hb ↦ (hh b hb).trans (hg b hb).symm⟩

theorem termValue_of_equal {n} (t : Semiterm L Empty n) {ts us : Fin n → ℕ}
    (he : ∀ i, C.Equal (ts i) (us i)) {r} (hr : C.TermValue t ts r) : C.TermValue t us r := by
  apply (C.termValue_iff t us r).mpr
  apply C.eval_of_equal _ (ts := r :> ts) (us := r :> us) ?_ ((C.termValue_iff t ts r).mp hr)
  exact Fin.cases (C.equal_refl r) he

theorem termCoordinate_congr {n} (t : Semiterm L Empty n) {ts us : Fin n → ℕ}
    (he : ∀ i, C.Equal (ts i) (us i)) :
    C.classOf (C.termCoordinate t ts) = C.classOf (C.termCoordinate t us) := by
  apply C.classOf_eq_iff.mpr
  exact C.termValue_unique (C.termValue_of_equal t he (C.termCoordinate_value t ts))
    (C.termCoordinate_value t us)

noncomputable instance extensionStructure : Structure L C.Domain where
  func := fun _ f b ↦ C.classOf (C.termCoordinate (.func f (fun i ↦ .bvar i)) (fun i ↦ (b i).out))
  rel := fun _ r b ↦ C.QuotientEval (ParameterInstance.atom r) b

@[simp] theorem func_classOf {n} (f : L.Func n) (ts : Fin n → ℕ) :
    Structure.func (self := C.extensionStructure) f (C.classOf ∘ ts) =
      C.classOf (C.termCoordinate (.func f (fun i ↦ .bvar i)) ts) := by
  apply C.termCoordinate_congr
  intro i
  exact C.classOf_eq_iff.mp (Quotient.out_eq (C.classOf (ts i)))

@[simp] theorem rel_classOf {n} (r : L.Rel n) (ts : Fin n → ℕ) :
    Structure.rel (self := C.extensionStructure) r (C.classOf ∘ ts) ↔
      C.Eval (ParameterInstance.atom r) ts := C.quotientEval_classOf _ _

theorem eval_ofFormula_equal {n} (i j : Fin n) (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFormula (Formula.equal i j) (FragmentClosure.fo_closed _)) ts ↔
      C.Equal (ts i) (ts j) := by
  constructor
  · rintro ⟨k, ht, hh⟩
    refine ⟨k, ht i, ht j, ?_⟩
    intro b hb
    exact (Formula.weakEval_equal M.Q i j _).mp ((ParameterInstance.eval_ofFormula _ _ _).mp (hh b hb))
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := C.coordinate_cofinal (RightCoordinate.width ts)
    obtain ⟨hi, hj, hh⟩ := equalAt_persistent (C.refines (Nat.le_max_left k l)) hk
    have hg := (C.refines (Nat.le_max_right k l)).choose
    have ht (i : Fin n) : ts i < 1 + (C.point (max k l)).1 :=
      (RightCoordinate.lt_width ts i).trans_le (hl.trans (Nat.add_le_add_left hg 1))
    refine ⟨max k l, ht, ?_⟩
    intro b hb
    exact (ParameterInstance.eval_ofFormula _ _ _).mpr ((Formula.weakEval_equal _ _ _ _).mpr (hh b hb))

instance extensionStructure_eq : Structure.Eq L C.Domain where
  eq a b := by
    change Structure.rel (self := C.extensionStructure) Language.Eq.eq ![a, b] ↔ a = b
    let ts : Fin 2 → ℕ := ![a.out, b.out]
    have he : C.classOf ∘ ts = ![a, b] := by
      funext i
      fin_cases i <;> exact Quotient.out_eq _
    rw [← he, C.rel_classOf]
    have ha : ParameterInstance.atom (M := M) (S := S) Language.Eq.eq =
        ParameterInstance.ofFormula (Formula.equal (0 : Fin 2) 1) (FragmentClosure.fo_closed _) := by
      have ht : (fun i : Fin 2 ↦ (Semiterm.bvar i : Semiterm L Empty 2)) = ![.bvar 0, .bvar 1] := by
        funext i
        fin_cases i <;> rfl
      exact congrArg (fun us ↦ ParameterInstance.ofFirstOrder (.rel Language.Eq.eq us)) ht
    rw [ha, C.eval_ofFormula_equal, ← C.classOf_eq_iff]
    exact Iff.of_eq (congrArg₂ Eq (Quotient.out_eq a) (Quotient.out_eq b))

end AdequateGenericChain
end WeakModel
end ZFVP.Infinitary
