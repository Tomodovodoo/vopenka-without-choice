import ZFVP.SetTheory.BoundedCodeExpressions
import ZFVP.Syntax.MembershipAtomicSyntax

/-! The concrete syntax-code constructors as boundedly definable expressions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace CodeExpression

def tuple₂ {n : ℕ} (a b : CodeExpression n) : CodeExpression n :=
  .doubleton (.kpair (.num 0) a) (.kpair (.num 1) b)
def boundVar {n : ℕ} (i : CodeExpression n) : CodeExpression n := .kpair (.num 0) i
def relation {n : ℕ} (r : CodeExpression n) : CodeExpression n := .kpair (.num 1) r
def truth {n : ℕ} : CodeExpression n := .kpair (.num 0) (.num 0)
def falsity {n : ℕ} : CodeExpression n := .kpair (.num 1) (.num 0)
def atom {n : ℕ} (r a : CodeExpression n) : CodeExpression n := .kpair (.num 2) (.kpair r a)
def negAtom {n : ℕ} (r a : CodeExpression n) : CodeExpression n := .kpair (.num 3) (.kpair r a)
def conj {n : ℕ} (φ ψ : CodeExpression n) : CodeExpression n := .kpair (.num 4) (.kpair φ ψ)
def disj {n : ℕ} (φ ψ : CodeExpression n) : CodeExpression n := .kpair (.num 5) (.kpair φ ψ)
def all {n : ℕ} (φ : CodeExpression n) : CodeExpression n := .kpair (.num 6) φ
def exs {n : ℕ} (φ : CodeExpression n) : CodeExpression n := .kpair (.num 7) φ
def boundArgs {n : ℕ} (i j : CodeExpression n) : CodeExpression n := tuple₂ (boundVar i) (boundVar j)
def guardArgs {n : ℕ} (i : CodeExpression n) : CodeExpression n := boundArgs (.num 0) (.succ i)
def boundedAll {n : ℕ} (i φ : CodeExpression n) : CodeExpression n :=
  all (disj (negAtom (relation (.num 1)) (guardArgs i)) φ)
def boundedExs {n : ℕ} (i φ : CodeExpression n) : CodeExpression n :=
  exs (conj (atom (relation (.num 1)) (guardArgs i)) φ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem standardTuple_two (a b : V) :
    standardTuple ![a, b] = SetTheory.doubleton ⟨(0 : V), a⟩ₖ ⟨(1 : V), b⟩ₖ := by
  apply mem_ext
  intro p
  rw [mem_standardTuple_iff, mem_doubleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
    · exact fun h ↦ Or.inl h
    · exact fun h ↦ Or.inr h
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

variable {n : ℕ} (v : Fin n → V)

@[simp] theorem eval_tuple₂ (a b : CodeExpression n) :
    (tuple₂ a b).eval v = standardTuple ![a.eval v, b.eval v] := by
  simp [tuple₂, eval, standardTuple_two]
@[simp] theorem eval_boundVar (i : CodeExpression n) : (boundVar i).eval v = boundVarCode (i.eval v) := rfl
@[simp] theorem eval_relation (r : CodeExpression n) : (relation r).eval v = relationToken (r.eval v) := rfl
@[simp] theorem eval_truth : (truth : CodeExpression n).eval v = (truthCode : V) := rfl
@[simp] theorem eval_falsity : (falsity : CodeExpression n).eval v = (falsityCode : V) := rfl
@[simp] theorem eval_atom (r a : CodeExpression n) : (atom r a).eval v = atomCode (r.eval v) (a.eval v) := rfl
@[simp] theorem eval_negAtom (r a : CodeExpression n) : (negAtom r a).eval v = negAtomCode (r.eval v) (a.eval v) := rfl
@[simp] theorem eval_conj (φ ψ : CodeExpression n) : (conj φ ψ).eval v = andCode (φ.eval v) (ψ.eval v) := rfl
@[simp] theorem eval_disj (φ ψ : CodeExpression n) : (disj φ ψ).eval v = orCode (φ.eval v) (ψ.eval v) := rfl
@[simp] theorem eval_all (φ : CodeExpression n) : (all φ).eval v = allCode (φ.eval v) := rfl
@[simp] theorem eval_exs (φ : CodeExpression n) : (exs φ).eval v = existsCode (φ.eval v) := rfl
@[simp] theorem eval_boundArgs (i j : CodeExpression n) :
    (boundArgs i j).eval v = boundPairArguments (i.eval v) (j.eval v) := by
  simp [boundArgs, boundPairArguments]
@[simp] theorem eval_guardArgs (i : CodeExpression n) :
    (guardArgs i).eval v = boundedGuardArguments (i.eval v) := by
  simp [guardArgs, boundPairArguments, boundedGuardArguments, eval]
@[simp] theorem eval_boundedAll (i φ : CodeExpression n) :
    (boundedAll i φ).eval v = boundedAllCode (i.eval v) (φ.eval v) := by
  simp [boundedAll, boundedAllCode, eval]
@[simp] theorem eval_boundedExs (i φ : CodeExpression n) :
    (boundedExs i φ).eval v = boundedExistsCode (i.eval v) (φ.eval v) := by
  simp [boundedExs, boundedExistsCode, eval]

end CodeExpression
end ZFVP
