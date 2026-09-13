import Mathlib.Data.Fin.VecNotation

/-!
Independent statement vocabulary for Theorem B. The only import is Mathlib.

ZF includes every parameter instance of separation and replacement. VP ranges
over all internally set-sized signatures, all definable proper classes, and
all internally finite formulas. The domain need not be externally well-founded
or countable. The proof-side dictionary files identify these definitions with
the existing formalization, including its internal satisfaction recursion.

The choices in `Coding` select sets or graphs specified by explicit membership
or recursion equations. The correspondence proofs establish existence and
uniqueness in every ZF model in each context where VP uses them.
-/

namespace PalomarBridge

/-- First-order formulas in the language of equality and membership.
Variables are de Bruijn indices. Quantifiers bind index zero. The constructors
use negation normal form; this imposes no restriction on first-order formulas. -/
inductive Formula : Nat → Type where
  | truth : Formula n
  | falsity : Formula n
  | equal : Fin n → Fin n → Formula n
  | unequal : Fin n → Fin n → Formula n
  | member : Fin n → Fin n → Formula n
  | nonmember : Fin n → Fin n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n
  | all : Formula (n + 1) → Formula n
  | exists_ : Formula (n + 1) → Formula n

/-- Ordinary satisfaction for an arbitrary membership relation on a domain.
Equality is equality of domain elements. No well-foundedness or external
countability condition is imposed on that domain. -/
def Formula.Realize {M : Type u} (mem : M → M → Prop) :
    {n : Nat} → Formula n → (Fin n → M) → Prop
  | _, .truth, _ => True
  | _, .falsity, _ => False
  | _, .equal i j, v => v i = v j
  | _, .unequal i j, v => v i ≠ v j
  | _, .member i j, v => mem (v i) (v j)
  | _, .nonmember i j, v => ¬mem (v i) (v j)
  | _, .conj p q, v => p.Realize mem v ∧ q.Realize mem v
  | _, .disj p q, v => p.Realize mem v ∨ q.Realize mem v
  | _, .all p, v => ∀ x, p.Realize mem (Fin.cons x v)
  | _, .exists_ p, v => ∃ x, p.Realize mem (Fin.cons x v)

/-- A sentence has no free variables. -/
abbrev Sentence := Formula 0

/-- A theory is a collection of sentences, including arbitrary axiom schemes. -/
abbrev Theory := Set Sentence

/-- Satisfaction of every axiom in a theory by an inhabited structure. -/
def Models {M : Type u} (mem : M → M → Prop) (T : Theory) : Prop :=
  Nonempty M ∧ ∀ p ∈ T, p.Realize mem Fin.elim0

/-- Existence of an inhabited set-sized model. This is semantic consistency;
completeness supplies its equivalence to the proof-theoretic consistency used
by the existing formalization. No external countability is assumed. -/
def Satisfiable (T : Theory) : Prop :=
  ∃ (M : Type) (mem : M → M → Prop), Models mem T

/-- Formulas with natural-number-indexed parameter variables. Every individual
formula uses finitely many parameters. Quantifiers bind only de Bruijn variables. -/
inductive OpenFormula : Nat → Type where
  | truth : OpenFormula n
  | falsity : OpenFormula n
  | equal : (Fin n ⊕ Nat) → (Fin n ⊕ Nat) → OpenFormula n
  | unequal : (Fin n ⊕ Nat) → (Fin n ⊕ Nat) → OpenFormula n
  | member : (Fin n ⊕ Nat) → (Fin n ⊕ Nat) → OpenFormula n
  | nonmember : (Fin n ⊕ Nat) → (Fin n ⊕ Nat) → OpenFormula n
  | conj : OpenFormula n → OpenFormula n → OpenFormula n
  | disj : OpenFormula n → OpenFormula n → OpenFormula n
  | all : OpenFormula (n + 1) → OpenFormula n
  | exists_ : OpenFormula (n + 1) → OpenFormula n

/-- Satisfaction with arbitrary parameter assignments. -/
def OpenFormula.Realize {M : Type u} (mem : M → M → Prop) (a : Nat → M) :
    {n : Nat} → OpenFormula n → (Fin n → M) → Prop
  | _, .truth, _ => True
  | _, .falsity, _ => False
  | _, .equal i j, v => Sum.elim v a i = Sum.elim v a j
  | _, .unequal i j, v => Sum.elim v a i ≠ Sum.elim v a j
  | _, .member i j, v => mem (Sum.elim v a i) (Sum.elim v a j)
  | _, .nonmember i j, v => ¬mem (Sum.elim v a i) (Sum.elim v a j)
  | _, .conj p q, v => p.Realize mem a v ∧ q.Realize mem a v
  | _, .disj p q, v => p.Realize mem a v ∨ q.Realize mem a v
  | _, .all p, v => ∀ x, p.Realize mem a (Fin.cons x v)
  | _, .exists_ p, v => ∃ x, p.Realize mem a (Fin.cons x v)

/-- Satisfaction of ZF in an arbitrary membership structure. Separation and
replacement range over all first-order formulas and all parameter assignments.
This definition does not require external well-foundedness or countability. -/
structure IsZF {M : Type u} (mem : M → M → Prop) : Prop where
  inhabited : Nonempty M
  empty : ∃ e, ∀ y, ¬mem y e
  extensionality : ∀ x y, x = y ↔ ∀ z, mem z x ↔ mem z y
  pairing : ∀ x y, ∃ z, ∀ w, mem w z ↔ w = x ∨ w = y
  union : ∀ x, ∃ y, ∀ z, mem z y ↔ ∃ w, mem w x ∧ mem z w
  power : ∀ x, ∃ y, ∀ z, mem z y ↔ ∀ w, mem w z → mem w x
  infinity : ∃ I, (∀ e, (∀ y, ¬mem y e) → mem e I) ∧
    (∀ x, mem x I → ∀ y, (∀ z, mem z y ↔ z = x ∨ mem z x) → mem y I)
  foundation : ∀ x, (∃ z, mem z x) → ∃ y, mem y x ∧ ∀ z, mem z x → ¬mem z y
  separation : ∀ (p : OpenFormula 1) (a : Nat → M) x,
    ∃ y, ∀ z, mem z y ↔ mem z x ∧ p.Realize mem a ![z]
  replacement : ∀ (p : OpenFormula 2) (a : Nat → M),
    (∀ x, ∃! y, p.Realize mem a ![x, y]) →
    ∀ X, ∃ Y, ∀ y, mem y Y ↔ ∃ x, mem x X ∧ p.Realize mem a ![x, y]

/-- The axiom of choice in the disjoint-family transversal form. -/
def HasChoice {M : Type u} (mem : M → M → Prop) : Prop :=
  ∀ family,
    (∀ X, mem X family → ∃ z, mem z X) ∧
    (∀ X, mem X family → ∀ Y, mem Y family → (∃ z, mem z X ∧ mem z Y) → X = Y) →
    ∃ C, ∀ X, mem X family → ∃! x, mem x C ∧ mem x X

namespace Coding
variable {M : Type u} (mem : M → M → Prop) [Nonempty M]

/-- The set with the specified elements, when that set exists. All uses below
are proved to exist in ZF. Extensionality makes the choice unique. -/
noncomputable def setValue (P : M → Prop) : M :=
  Classical.epsilon (fun s => ∀ x, mem x s ↔ P x)

noncomputable def empty : M := setValue mem (fun _ => False)
noncomputable def unordered (x y : M) : M := setValue mem (fun z => z = x ∨ z = y)
/-- Kuratowski ordered pairs. -/
noncomputable def pair (x y : M) : M := unordered mem (unordered mem x x) (unordered mem x y)
noncomputable def union (a : M) : M := setValue mem (fun x => ∃ y, mem y a ∧ mem x y)
noncomputable def inter (a : M) : M :=
  setValue mem (fun x => (∃ y, mem y a) ∧ ∀ y, mem y a → mem x y)
noncomputable def first (p : M) : M := union mem (inter mem p)
noncomputable def second (p : M) : M := union mem (setValue mem
  (fun x => mem x (union mem p) ∧ (mem x (inter mem p) → union mem p = inter mem p)))
noncomputable def succ (x : M) : M := setValue mem (fun z => z = x ∨ mem z x)
noncomputable def numeral : Nat → M
  | 0 => empty mem
  | n + 1 => succ mem (numeral n)

/-- Inductive sets contain zero and the successor of each of their elements. -/
def Inductive (a : M) : Prop :=
  mem (empty mem) a ∧ ∀ x, mem x a → mem (succ mem x) a
/-- The internal natural numbers, the intersection of all inductive sets.
The quantifier ranges over sets of the model, so nonstandard naturals are retained. -/
noncomputable def omega : M := setValue mem (fun x => ∀ a, Inductive mem a → mem x a)
noncomputable def domain (f : M) : M := setValue mem (fun x => ∃ y, mem (pair mem x y) f)
noncomputable def range (f : M) : M := setValue mem (fun y => ∃ x, mem (pair mem x y) f)
noncomputable def value (f x : M) : M :=
  setValue mem (fun z => ∃ y, mem z y ∧ mem (pair mem x y) f)

/-- The set of all internal function graphs from X to Y. -/
noncomputable def functions (Y X : M) : M := setValue mem (fun f =>
  (∀ p, mem p f → ∃ x, mem x X ∧ ∃ y, mem y Y ∧ p = pair mem x y) ∧
  ∀ x, mem x X → ∃! y, mem (pair mem x y) f)
def IsFunction (f : M) : Prop := mem f (functions mem (range mem f) (domain mem f))
noncomputable def compose (f g : M) : M := setValue mem (fun p =>
  ∃ x y z, p = pair mem x z ∧ mem (pair mem x y) f ∧ mem (pair mem y z) g)
noncomputable def restrict (f A : M) : M := setValue mem (fun p =>
  ∃ x, mem x A ∧ ∃ y, p = pair mem x y ∧ mem p f)

noncomputable def language (F R fa ra : M) : M := pair mem F (pair mem R (pair mem fa ra))
noncomputable def functionSymbols (L : M) : M := first mem L
noncomputable def relationSymbols (L : M) : M := first mem (second mem L)
noncomputable def functionArities (L : M) : M := first mem (second mem (second mem L))
noncomputable def relationArities (L : M) : M := second mem (second mem (second mem L))
/-- An internal set-sized signature, with internally natural arities. -/
def IsLanguage (L : M) : Prop :=
  L = language mem (functionSymbols mem L) (relationSymbols mem L)
    (functionArities mem L) (relationArities mem L) ∧
  mem (functionArities mem L) (functions mem (omega mem) (functionSymbols mem L)) ∧
  mem (relationArities mem L) (functions mem (omega mem) (relationSymbols mem L))
noncomputable def structureCode (A FI RI : M) : M := pair mem A (pair mem FI RI)
noncomputable def structureDomain (S : M) : M := first mem S
noncomputable def structureFunctions (S : M) : M := first mem (second mem S)
noncomputable def structureRelations (S : M) : M := second mem (second mem S)
/-- A nonempty internal structure, with total operations and relations of the
specified arities. All interpretation maps and their arguments are internal sets. -/
def IsStructure (L S : M) : Prop :=
  IsLanguage mem L ∧ S = structureCode mem (structureDomain mem S)
    (structureFunctions mem S) (structureRelations mem S) ∧
  (∃ x, mem x (structureDomain mem S)) ∧
  IsFunction mem (structureFunctions mem S) ∧
    domain mem (structureFunctions mem S) = functionSymbols mem L ∧
  IsFunction mem (structureRelations mem S) ∧
    domain mem (structureRelations mem S) = relationSymbols mem L ∧
  (∀ f, mem f (functionSymbols mem L) →
    mem (value mem (structureFunctions mem S) f)
      (functions mem (structureDomain mem S) (functions mem (structureDomain mem S)
        (value mem (functionArities mem L) f)))) ∧
  ∀ r, mem r (relationSymbols mem L) → ∀ t,
    mem t (value mem (structureRelations mem S) r) →
    mem t (functions mem (structureDomain mem S) (value mem (relationArities mem L) r))

noncomputable def boundVar (i : M) : M := pair mem (numeral mem 0) i
noncomputable def functionTerm (f args : M) : M := pair mem (numeral mem 2) (pair mem f args)
/-- Closure under bound variables and applications for formulas without free
internal variables. External parameters of VP are handled by `Formula.Realize`. -/
def TermClosed (L n T : M) : Prop :=
  (∀ i, mem i n → mem (boundVar mem i) T) ∧
  ∀ f, mem f (functionSymbols mem L) → ∀ args,
    mem args (functions mem T (value mem (functionArities mem L) f)) →
    mem (functionTerm mem f args) T
/-- The least internally closed term set. -/
noncomputable def terms (L n : M) : M :=
  setValue mem (fun t => ∀ T, TermClosed mem L n T → mem t T)
noncomputable def truthCode : M := pair mem (numeral mem 0) (empty mem)
noncomputable def falsityCode : M := pair mem (numeral mem 1) (empty mem)
noncomputable def atom (r args : M) : M := pair mem (numeral mem 2) (pair mem r args)
noncomputable def negAtom (r args : M) : M := pair mem (numeral mem 3) (pair mem r args)
noncomputable def conjunction (p q : M) : M := pair mem (numeral mem 4) (pair mem p q)
noncomputable def disjunction (p q : M) : M := pair mem (numeral mem 5) (pair mem p q)
noncomputable def universal (p : M) : M := pair mem (numeral mem 6) p
noncomputable def existential (p : M) : M := pair mem (numeral mem 7) p
/-- Equality has the empty token; relation symbols have a distinct tag. -/
def AtomicArguments (L n r args : M) : Prop :=
  (r = empty mem ∧ mem args (functions mem (terms mem L n) (numeral mem 2))) ∨
  ∃ s, mem s (relationSymbols mem L) ∧ r = pair mem (numeral mem 1) s ∧
    mem args (functions mem (terms mem L n) (value mem (relationArities mem L) s))
def FormulaClosed (L Q : M) : Prop := ∀ n, mem n (omega mem) →
  (mem (pair mem n (truthCode mem)) Q ∧ mem (pair mem n (falsityCode mem)) Q) ∧
  (∀ r args, AtomicArguments mem L n r args →
    mem (pair mem n (atom mem r args)) Q ∧ mem (pair mem n (negAtom mem r args)) Q) ∧
  (∀ p q, mem (pair mem n p) Q → mem (pair mem n q) Q →
    mem (pair mem n (conjunction mem p q)) Q ∧ mem (pair mem n (disjunction mem p q)) Q) ∧
  ∀ p, mem (pair mem (succ mem n) p) Q →
    mem (pair mem n (universal mem p)) Q ∧ mem (pair mem n (existential mem p)) Q
/-- The least internal family of context/formula pairs. This includes every
internally finite formula, even when the ambient model is externally ill-founded. -/
noncomputable def formulas (L : M) : M :=
  setValue mem (fun p => ∀ Q, FormulaClosed mem L Q → mem p Q)

noncomputable def predecessors (R D x : M) : M :=
  setValue mem (fun y => mem y D ∧ mem (pair mem y x) R)
noncomputable def subterms (T : M) : M := setValue mem (fun p =>
  ∃ s t, p = pair mem s t ∧ mem s T ∧ mem t T ∧
    ∃ f args, t = functionTerm mem f args ∧ mem s (range mem args))
noncomputable def termStep (S b t previous : M) : M := by
  classical
  exact if first mem t = numeral mem 0 then value mem b (second mem t)
    else if first mem t = numeral mem 1 then value mem (empty mem) (second mem t)
    else value mem (value mem (structureFunctions mem S) (first mem (second mem t)))
      (compose mem (second mem (second mem t)) previous)
/-- The internal term evaluation graph is uniquely specified by recursion on
immediate subterms. Quantification over the whole graph is internal to the model. -/
def TermEvaluationGraph (L n S b g : M) : Prop :=
  IsFunction mem g ∧ domain mem g = terms mem L n ∧
  ∀ t, mem t (terms mem L n) → value mem g t = termStep mem S b t
    (restrict mem g (predecessors mem (subterms mem (terms mem L n)) (terms mem L n) t))
noncomputable def termEvaluation (L n S b : M) : M :=
  Classical.epsilon (TermEvaluationGraph mem L n S b)
noncomputable def evaluatedArguments (L S n b args : M) : M :=
  compose mem args (termEvaluation mem L n S b)
def AtomicHolds (L S n b r args : M) : Prop :=
  (r = empty mem ∧ value mem (evaluatedArguments mem L S n b args) (numeral mem 0) =
    value mem (evaluatedArguments mem L S n b args) (numeral mem 1)) ∨
  ∃ s, mem s (relationSymbols mem L) ∧ r = pair mem (numeral mem 1) s ∧
    mem (evaluatedArguments mem L S n b args) (value mem (structureRelations mem S) s)

noncomputable def prependValue (b x i : M) : M := by
  classical
  exact if i = numeral mem 0 then x else value mem b (union mem i)
noncomputable def prepend (n b x : M) : M := setValue mem (fun p =>
  ∃ i, mem i (succ mem n) ∧ p = pair mem i (prependValue mem b x i))
/-- Immediate subformulas record their variable contexts. Quantifier bodies
have one more variable than the parent formula. -/
def ImmediateSubformula (s t : M) : Prop :=
  (∃ n p q, (t = pair mem n (conjunction mem p q) ∨ t = pair mem n (disjunction mem p q)) ∧
    (s = pair mem n p ∨ s = pair mem n q)) ∨
  ∃ n p, (t = pair mem n (universal mem p) ∨ t = pair mem n (existential mem p)) ∧
    s = pair mem (succ mem n) p
noncomputable def subformulas (F : M) : M := setValue mem (fun p =>
  ∃ s t, p = pair mem s t ∧ mem s F ∧ mem t F ∧ ImmediateSubformula mem s t)
/-- Tarski's clauses, including quantification over every element of the internal
domain and every internally finite assignment. Falsity has no satisfying clause. -/
def SatisfactionStep (L S p previous b : M) : Prop :=
  second mem p = truthCode mem ∨
  (∃ r args, second mem p = atom mem r args ∧ AtomicHolds mem L S (first mem p) b r args) ∨
  (∃ r args, second mem p = negAtom mem r args ∧ ¬AtomicHolds mem L S (first mem p) b r args) ∨
  (∃ q r, second mem p = conjunction mem q r ∧
    mem b (value mem previous (pair mem (first mem p) q)) ∧
    mem b (value mem previous (pair mem (first mem p) r))) ∨
  (∃ q r, second mem p = disjunction mem q r ∧
    (mem b (value mem previous (pair mem (first mem p) q)) ∨
     mem b (value mem previous (pair mem (first mem p) r)))) ∨
  (∃ q, second mem p = universal mem q ∧ ∀ x, mem x (structureDomain mem S) →
    mem (prepend mem (first mem p) b x) (value mem previous (pair mem (succ mem (first mem p)) q))) ∨
  ∃ q, second mem p = existential mem q ∧ ∃ x, mem x (structureDomain mem S) ∧
    mem (prepend mem (first mem p) b x) (value mem previous (pair mem (succ mem (first mem p)) q))
/-- A set-coded truth graph satisfying Tarski's clauses on the whole internal
formula family. This specifies the graph uniquely in every ZF model. -/
def SatisfactionGraph (L S g : M) : Prop :=
  IsFunction mem g ∧ domain mem g = formulas mem L ∧
  ∀ p, mem p (formulas mem L) → ∀ b,
    mem b (value mem g p) ↔ mem b (functions mem (structureDomain mem S) (first mem p)) ∧
      SatisfactionStep mem L S p
        (restrict mem g (predecessors mem (subformulas mem (formulas mem L)) (formulas mem L) p)) b
noncomputable def satisfaction (L S : M) : M := Classical.epsilon (SatisfactionGraph mem L S)
def Holds (L S n p b : M) : Prop := mem b (value mem (satisfaction mem L S) (pair mem n p))
/-- An internal graph preserving all internally finite formulas. -/
def Elementary (L S T f : M) : Prop :=
  IsStructure mem L S ∧ IsStructure mem L T ∧
  mem f (functions mem (structureDomain mem T) (structureDomain mem S)) ∧
  ∀ n, mem n (omega mem) → ∀ p, mem (pair mem n p) (formulas mem L) →
    ∀ b, mem b (functions mem (structureDomain mem S) n) →
      (Holds mem L S n p b ↔ Holds mem L T n p (compose mem b f))
/-- Parameterized Vopěnka scheme for every internally set-sized language.
The class is proper when no internal set contains all of its members. -/
def Vopenka : Prop := ∀ (p : Formula 2) (L a : M),
  (∀ A, ∃ S, p.Realize mem ![S, a] ∧ ¬mem S A) →
  (∀ S, p.Realize mem ![S, a] → IsStructure mem L S) →
  ∃ S T f, S ≠ T ∧ p.Realize mem ![S, a] ∧ p.Realize mem ![T, a] ∧ Elementary mem L S T f

end Coding
/-- Existence of a set-sized model of ZF plus the full parameterized VP scheme. -/
def HasZFVPModel : Prop :=
  ∃ (M : Type) (mem : M → M → Prop) (hne : Nonempty M),
    IsZF mem ∧ @Coding.Vopenka M mem hne

/-- Existence of a set-sized model of ZFC plus the same VP scheme. -/
def HasZFCVPModel : Prop :=
  ∃ (M : Type) (mem : M → M → Prop) (hne : Nonempty M),
    IsZF mem ∧ HasChoice mem ∧ @Coding.Vopenka M mem hne

end PalomarBridge







