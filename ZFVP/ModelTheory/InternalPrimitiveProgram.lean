import ZFVP.Syntax.PrimitiveProgram
import ZFVP.ModelTheory.InternalPrimitiveRecursion

/-! Uniform, total interpretations of explicit primitive-recursive programs in internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

def formula : PrimitiveProgram → SetTheorySemisentence 2
  | .zero => “y x. !isEmpty y”
  | .succ => f“y x. y = !succ.dfn x”
  | .left => naturalSquareLeftFormula
  | .right => naturalSquareRightFormula
  | .pair a b => f“y x. y = !naturalSquarePairFormula (!a.formula x) (!b.formula x)”
  | .comp a b => f“y x. y = !a.formula (!b.formula x)”
  | .prec a b => naturalPrecFormula a.formula b.formula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure Realization (c : PrimitiveProgram) where
  func : V → V
  defined : ℒₛₑₜ-function₁ func via c.formula
  natural : ∀ x ∈ (ω : V), func x ∈ (ω : V)
  standard : ∀ n : ℕ, func (n : V) = (c.eval n : V)

noncomputable def realization (c : PrimitiveProgram) : Realization (V := V) c := by
  induction c with
  | zero =>
    refine ⟨fun _ ↦ 0, ⟨fun v ↦ by simp [formula, zero_def]⟩, fun _ _ ↦ by simp, ?_⟩
    intro n
    rfl
  | succ =>
    refine ⟨SetTheory.succ, ⟨fun v ↦ by simp [formula]⟩, fun _ h ↦ ω_succ_closed h, ?_⟩
    intro n
    exact (num_succ_def n).symm
  | left =>
    refine ⟨naturalSquareLeft, naturalSquareLeft_defined, fun _ _ ↦ naturalSquareLeft_natural _, ?_⟩
    intro n
    exact congrArg Prod.fst (naturalSquareUnpair_natCast n)
  | right =>
    refine ⟨naturalSquareRight, naturalSquareRight_defined, fun _ _ ↦ naturalSquareRight_natural _, ?_⟩
    intro n
    exact congrArg Prod.snd (naturalSquareUnpair_natCast n)
  | pair a b ha hb =>
    let : ℒₛₑₜ-function₁ ha.func via a.formula := ha.defined
    let : ℒₛₑₜ-function₁ hb.func via b.formula := hb.defined
    refine ⟨fun x ↦ naturalSquarePair (ha.func x) (hb.func x),
      ⟨fun v ↦ by simp [formula]⟩,
      fun x hx ↦ naturalSquarePair_natural (ha.natural x hx) (hb.natural x hx), ?_⟩
    intro n
    rw [ha.standard, hb.standard, naturalSquarePair_natCast]
    rfl
  | comp a b ha hb =>
    let : ℒₛₑₜ-function₁ ha.func via a.formula := ha.defined
    let : ℒₛₑₜ-function₁ hb.func via b.formula := hb.defined
    refine ⟨fun x ↦ ha.func (hb.func x), ⟨fun v ↦ by simp [formula]⟩,
      fun x hx ↦ ha.natural _ (hb.natural x hx), ?_⟩
    intro n
    rw [hb.standard, ha.standard]
    rfl
  | prec a b ha hb =>
    let : ℒₛₑₜ-function₁ ha.func via a.formula := ha.defined
    let : ℒₛₑₜ-function₁ hb.func via b.formula := hb.defined
    refine ⟨naturalPrec ha.func hb.func ha.defined.to_definable hb.defined.to_definable,
      naturalPrec_defined ha.func hb.func a.formula b.formula,
      fun x _ ↦ naturalPrec_natural _ _ _ _ ha.natural hb.natural x, ?_⟩
    intro n
    exact naturalPrec_natCast _ _ _ _ a.eval b.eval ha.standard hb.standard n

noncomputable def evalSet (c : PrimitiveProgram) : V → V := c.realization.func

instance evalSet_defined (c : PrimitiveProgram) : ℒₛₑₜ-function₁[V] c.evalSet via c.formula := c.realization.defined

instance evalSet_definable (c : PrimitiveProgram) : ℒₛₑₜ-function₁[V] c.evalSet := (evalSet_defined c).to_definable

theorem evalSet_natural (c : PrimitiveProgram) {x : V} (hx : x ∈ (ω : V)) : c.evalSet x ∈ (ω : V) :=
  c.realization.natural x hx

theorem evalSet_natCast (c : PrimitiveProgram) (n : ℕ) : c.evalSet (n : V) = (c.eval n : V) :=
  c.realization.standard n

theorem eval_formula_iff (c : PrimitiveProgram) (x y : V) : c.formula.Evalb ![y, x] ↔ y = c.evalSet x :=
  (evalSet_defined c).iff ![y, x]

theorem formula_total (c : PrimitiveProgram) (x : V) : ∃! y : V, c.formula.Evalb ![y, x] := by
  simp only [eval_formula_iff]
  exact existsUnique_eq

end PrimitiveProgram
end ZFVP
