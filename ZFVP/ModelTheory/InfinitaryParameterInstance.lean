import ZFVP.ModelTheory.InfinitaryAdequateModel
import Mathlib.Data.Fin.VecNotation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]

/-- A fragment template with only finitely many named old parameters. -/
def ParameterInstance (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) (n : ℕ) :=
  Σ k : ℕ, {φ : Formula L (n + k) //
    ⟨n + k, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)} × (Fin k → M.Domain)

namespace ParameterInstance
variable {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

theorem countable (hS : S.Countable) (n : ℕ) : Countable (ParameterInstance M S n) := by
  have hT := FragmentClosure.carrier_countable (SequenceClosure.carrier_countable hS)
  have : Countable (FragmentClosure.carrier (SequenceClosure.carrier S)) := hT.to_subtype
  have (k : ℕ) : Countable {φ : Formula L (n + k) //
      ⟨n + k, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)} :=
    Function.Injective.countable (f := fun φ ↦ (⟨⟨n + k, φ.1⟩, φ.2⟩ :
      FragmentClosure.carrier (SequenceClosure.carrier S))) (by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h)
  unfold ParameterInstance
  infer_instance

def Eval {n} (p : ParameterInstance M S n) (a : Fin n → M.Domain) : Prop :=
  Formula.WeakEval M.Q p.2.1.1 (Fin.append a p.2.2)

def neg {n} (p : ParameterInstance M S n) : ParameterInstance M S n :=
  ⟨p.1, ⟨⟨.neg p.2.1.1, FragmentClosure.neg_closed p.2.1.2⟩, p.2.2⟩⟩

@[simp] theorem eval_neg {n} (p : ParameterInstance M S n) (a : Fin n → M.Domain) :
    p.neg.Eval a ↔ ¬p.Eval a := Iff.rfl

/-- Rename the free slots, retaining exactly the same finite parameter tuple. -/
def rename {n m} (p : ParameterInstance M S n) (ρ : Fin n → Fin m) :
    ParameterInstance M S m :=
  ⟨p.1, ⟨⟨p.2.1.1.rename (Fin.addCases (fun i ↦ Fin.castAdd p.1 (ρ i)) (Fin.natAdd m)),
    FragmentClosure.rename_closed p.2.1.2 _⟩, p.2.2⟩⟩

@[simp] theorem eval_rename {n m} (p : ParameterInstance M S n) (ρ : Fin n → Fin m)
    (a : Fin m → M.Domain) : (p.rename ρ).Eval a ↔ p.Eval (a ∘ ρ) := by
  unfold Eval rename
  rw [Formula.weakEval_rename]
  apply Iff.of_eq
  congr 1
  funext i
  cases i using Fin.addCases <;> simp [Function.comp_def]

omit [L.Encodable] in
theorem cons_append {n k} (x : M.Domain) (a : Fin n → M.Domain)
    (b : Fin k → M.Domain) :
    (x :> Fin.append a b) ∘ Fin.cast (show n + 1 + k = n + k + 1 by omega) =
      Fin.append (x :> a) b := by
  have h := Matrix.cons_vecAppend (m := n) (n := k) (o := n + k) (by omega) x a b
  dsimp [Matrix.vecAppend] at h
  have h' := congrArg (fun f ↦ f ∘ Fin.cast (show n + 1 + k = n + k + 1 by omega)) h
  simpa [Function.comp_def, Matrix.vecCons, Fin.cast_cast] using h'.symm

def exs {n} (p : ParameterInstance M S (n + 1)) : ParameterInstance M S n :=
  ⟨p.1, ⟨⟨.exs (p.2.1.1.rename (Fin.cast (by omega))),
    FragmentClosure.exs_closed (FragmentClosure.rename_closed p.2.1.2 _)⟩, p.2.2⟩⟩

@[simp] theorem eval_exs {n} (p : ParameterInstance M S (n + 1)) (a : Fin n → M.Domain) :
    p.exs.Eval a ↔ ∃ x, p.Eval (x :> a) := by
  unfold Eval exs
  simp only [Formula.weakEval_exs, Formula.weakEval_rename, cons_append]

def q {n} (p : ParameterInstance M S (n + 1)) : ParameterInstance M S n :=
  ⟨p.1, ⟨⟨.q (p.2.1.1.rename (Fin.cast (by omega))),
    FragmentClosure.q_closed (FragmentClosure.rename_closed p.2.1.2 _)⟩, p.2.2⟩⟩

@[simp] theorem eval_q {n} (p : ParameterInstance M S (n + 1)) (a : Fin n → M.Domain) :
    p.q.Eval a ↔ M.Q {x | p.Eval (x :> a)} := by
  unfold Eval q
  simp only [Formula.weakEval_q, Formula.weakEval_rename, cons_append]


def ofFormula {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ParameterInstance M S n := ⟨0, ⟨⟨φ, hφ⟩, Fin.elim0⟩⟩

omit [L.Encodable] in
@[simp] theorem eval_ofFormula {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (a : Fin n → M.Domain) : (ofFormula φ hφ).Eval a ↔ Formula.WeakEval M.Q φ a := by
  simp [Eval, ofFormula, Fin.append_right_nil, Function.comp_def]

/-- Binary combination uses the union of two finite name lists. -/
def and {n} (p q : ParameterInstance M S n) : ParameterInstance M S n :=
  ⟨p.1 + q.1, ⟨⟨
    (p.2.1.1.rename (Fin.addCases (Fin.castAdd (p.1 + q.1))
      (fun i ↦ Fin.natAdd n (Fin.castAdd q.1 i)))).and
    (q.2.1.1.rename (Fin.addCases (Fin.castAdd (p.1 + q.1))
      (fun i ↦ Fin.natAdd n (Fin.natAdd p.1 i)))),
    FragmentClosure.and_closed (FragmentClosure.rename_closed p.2.1.2 _)
      (FragmentClosure.rename_closed q.2.1.2 _)⟩, Fin.append p.2.2 q.2.2⟩⟩

@[simp] theorem eval_and {n} (p q : ParameterInstance M S n) (a : Fin n → M.Domain) :
    (p.and q).Eval a ↔ p.Eval a ∧ q.Eval a := by
  unfold Eval and
  simp only [Formula.weakEval_and, Formula.weakEval_rename]
  have hp : Fin.append a (Fin.append p.2.2 q.2.2) ∘
      Fin.addCases (Fin.castAdd (p.1 + q.1)) (fun i ↦ Fin.natAdd n (Fin.castAdd q.1 i)) =
      Fin.append a p.2.2 := by
    funext i
    cases i using Fin.addCases <;> simp [Function.comp_def]
  have hq : Fin.append a (Fin.append p.2.2 q.2.2) ∘
      Fin.addCases (Fin.castAdd (p.1 + q.1)) (fun i ↦ Fin.natAdd n (Fin.natAdd p.1 i)) =
      Fin.append a q.2.2 := by
    funext i
    cases i using Fin.addCases <;> simp [Function.comp_def]
  rw [hp, hq]

def all {n} (p : ParameterInstance M S (n + 1)) : ParameterInstance M S n := p.neg.exs.neg

@[simp] theorem eval_all {n} (p : ParameterInstance M S (n + 1)) (a : Fin n → M.Domain) :
    p.all.Eval a ↔ ∀ x, p.Eval (x :> a) := by
  simp [all]

end ParameterInstance

/-- One represented conjunction template with one finite tuple shared by every
component. An arbitrary sequence of individually named instances is not a code. -/
def ParameterSequence (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) (n : ℕ) :=
  Σ k : ℕ, {f : ℕ → Formula L (n + k) //
    ⟨n + k, Formula.conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)} ×
      (Fin k → M.Domain)

namespace ParameterSequence
variable {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

def conj {n} (p : ParameterSequence M S n) : ParameterInstance M S n :=
  ⟨p.1, ⟨⟨.conj p.2.1.1, p.2.1.2⟩, p.2.2⟩⟩

omit [L.Encodable] in
theorem conj_injective {n} : Function.Injective (conj (M := M) (S := S) (n := n)) := by
  rintro ⟨k, ⟨⟨f, hf⟩, b⟩⟩ ⟨l, ⟨⟨g, hg⟩, c⟩⟩ he
  have hkl : k = l := congrArg Sigma.fst he
  subst l
  have h := Sigma.mk.inj_iff.mp he
  have hp := eq_of_heq h.2
  have hfg : f = g := Formula.conj.inj (congrArg (fun z ↦ z.1.1) hp)
  have hbc : b = c := congrArg Prod.snd hp
  subst g
  subst c
  rfl

theorem countable (hS : S.Countable) (n : ℕ) : Countable (ParameterSequence M S n) := by
  have := ParameterInstance.countable (M := M) hS n
  exact Function.Injective.countable conj_injective

def component {n} (p : ParameterSequence M S n) (i : ℕ) : ParameterInstance M S n :=
  ⟨p.1, ⟨⟨p.2.1.1 i, FragmentClosure.subformulas_closed p.2.1.2 (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas _⟩))⟩, p.2.2⟩⟩

@[simp] theorem eval_conj {n} (p : ParameterSequence M S n) (a : Fin n → M.Domain) :
    p.conj.Eval a ↔ ∀ i, (p.component i).Eval a := Iff.rfl


def neg {n} (p : ParameterSequence M S n) : ParameterSequence M S n :=
  ⟨p.1, ⟨⟨fun i ↦ .neg (p.2.1.1 i), by
    have h := p.2.1.2
    simp only [SequenceClosure.base_carrier_eq] at h ⊢
    exact SequenceClosure.conj_neg_closed h⟩, p.2.2⟩⟩

@[simp] theorem eval_neg_component {n} (p : ParameterSequence M S n) (i : ℕ)
    (a : Fin n → M.Domain) : (p.neg.component i).Eval a ↔ ¬(p.component i).Eval a := Iff.rfl

def exs {n} (p : ParameterSequence M S (n + 1)) : ParameterSequence M S n :=
  ⟨p.1, ⟨⟨fun i ↦ .exs ((p.2.1.1 i).rename (Fin.cast (by omega))), by
    have h := FragmentClosure.rename_closed p.2.1.2
      (Fin.cast (show n + 1 + p.1 = n + p.1 + 1 by omega))
    simp only [SequenceClosure.base_carrier_eq] at h ⊢
    exact SequenceClosure.conj_exs_closed h⟩, p.2.2⟩⟩

@[simp] theorem eval_exs_component {n} (p : ParameterSequence M S (n + 1)) (i : ℕ)
    (a : Fin n → M.Domain) : (p.exs.component i).Eval a ↔ ∃ x, (p.component i).Eval (x :> a) :=
  ParameterInstance.eval_exs (p.component i) a

def q {n} (p : ParameterSequence M S (n + 1)) : ParameterSequence M S n :=
  ⟨p.1, ⟨⟨fun i ↦ .q ((p.2.1.1 i).rename (Fin.cast (by omega))), by
    have h := FragmentClosure.rename_closed p.2.1.2
      (Fin.cast (show n + 1 + p.1 = n + p.1 + 1 by omega))
    simp only [SequenceClosure.base_carrier_eq] at h ⊢
    exact SequenceClosure.conj_q_closed h⟩, p.2.2⟩⟩

@[simp] theorem eval_q_component {n} (p : ParameterSequence M S (n + 1)) (i : ℕ)
    (a : Fin n → M.Domain) : (p.q.component i).Eval a ↔ M.Q {x | (p.component i).Eval (x :> a)} :=
  ParameterInstance.eval_q (p.component i) a


/-- A fixed additional formula adds only its finite list of names to the common support. -/
def andLeft {n} (p : ParameterInstance M S n) (s : ParameterSequence M S n) :
    ParameterSequence M S n :=
  ⟨p.1 + s.1, ⟨⟨fun i ↦
    (p.2.1.1.rename (Fin.addCases (Fin.castAdd (p.1 + s.1))
      (fun j ↦ Fin.natAdd n (Fin.castAdd s.1 j)))).and
    ((s.2.1.1 i).rename (Fin.addCases (Fin.castAdd (p.1 + s.1))
      (fun j ↦ Fin.natAdd n (Fin.natAdd p.1 j)))), by
    have hp := FragmentClosure.rename_closed p.2.1.2
      (Fin.addCases (Fin.castAdd (p.1 + s.1)) (fun j ↦ Fin.natAdd n (Fin.castAdd s.1 j)))
    have hs := FragmentClosure.rename_closed s.2.1.2
      (Fin.addCases (Fin.castAdd (p.1 + s.1)) (fun j ↦ Fin.natAdd n (Fin.natAdd p.1 j)))
    simp only [SequenceClosure.base_carrier_eq] at hp hs ⊢
    exact SequenceClosure.conj_and_closed hs hp⟩, Fin.append p.2.2 s.2.2⟩⟩

@[simp] theorem eval_andLeft_component {n} (p : ParameterInstance M S n)
    (s : ParameterSequence M S n) (i : ℕ) (a : Fin n → M.Domain) :
    ((andLeft p s).component i).Eval a ↔ p.Eval a ∧ (s.component i).Eval a :=
  ParameterInstance.eval_and p (s.component i) a

def rename {n m} (s : ParameterSequence M S n) (ρ : Fin n → Fin m) :
    ParameterSequence M S m :=
  ⟨s.1, ⟨⟨fun i ↦ (s.2.1.1 i).rename
    (Fin.addCases (fun j ↦ Fin.castAdd s.1 (ρ j)) (Fin.natAdd m)),
    FragmentClosure.rename_closed s.2.1.2 _⟩, s.2.2⟩⟩

@[simp] theorem eval_rename_component {n m} (s : ParameterSequence M S n)
    (ρ : Fin n → Fin m) (i : ℕ) (a : Fin m → M.Domain) :
    ((s.rename ρ).component i).Eval a ↔ (s.component i).Eval (a ∘ ρ) :=
  ParameterInstance.eval_rename (s.component i) ρ a

end ParameterSequence
end WeakModel
end ZFVP.Infinitary

