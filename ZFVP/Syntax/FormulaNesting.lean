import Foundation.FirstOrder.Basic.BinderNotation

namespace ZFVP
open LO.FirstOrder Semiformula
variable {L : Language} {ξ M : Type*} [Structure L M] {m : ℕ} {e : Fin m → M} {f : ξ → M} {z : M}

@[simp] theorem eval_nestedRelation5
    {φ : Semiformula L ξ 5} {p1 p2 p3 p4 p5 : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![p1, p2, p3, p4, p5]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      Eval ![x1, x2, x3, x4, x5] f φ := by
  suffices (∀ x1 x2 x3 x4 x5, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval ![x1, x2, x3, x4, x5] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      Eval ![x1, x2, x3, x4, x5] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5
    exact h x1 x2 x3 x4 x5 h1 h2 h3 h4 h5
  · intro h x1 x2 x3 x4 x5 h1 h2 h3 h4 h5
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5

@[simp] theorem eval_nestedFunction5
    {φ : Semiformula L ξ 6} {p1 p2 p3 p4 p5 : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![p1, p2, p3, p4, p5]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      Eval ![z, x1, x2, x3, x4, x5] f φ := by
  suffices (∀ x1 x2 x3 x4 x5, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval ![z, x1, x2, x3, x4, x5] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      Eval ![z, x1, x2, x3, x4, x5] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5
    exact h x1 x2 x3 x4 x5 h1 h2 h3 h4 h5
  · intro h x1 x2 x3 x4 x5 h1 h2 h3 h4 h5
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5

@[simp] theorem eval_nestedRelation6
    {φ : Semiformula L ξ 6} {p1 p2 p3 p4 p5 p6 : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![p1, p2, p3, p4, p5, p6]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      Eval ![x1, x2, x3, x4, x5, x6] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval ![x1, x2, x3, x4, x5, x6] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      Eval ![x1, x2, x3, x4, x5, x6] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6
    exact h x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
  · intro h x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6

@[simp] theorem eval_nestedFunction6
    {φ : Semiformula L ξ 7} {p1 p2 p3 p4 p5 p6 : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![p1, p2, p3, p4, p5, p6]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      Eval ![z, x1, x2, x3, x4, x5, x6] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval ![z, x1, x2, x3, x4, x5, x6] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      Eval ![z, x1, x2, x3, x4, x5, x6] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6
    exact h x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
  · intro h x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6

@[simp] theorem eval_nestedRelation7
    {φ : Semiformula L ξ 7} {p1 p2 p3 p4 p5 p6 p7 : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![p1, p2, p3, p4, p5, p6, p7]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      Eval ![x1, x2, x3, x4, x5, x6, x7] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval ![x1, x2, x3, x4, x5, x6, x7] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      Eval ![x1, x2, x3, x4, x5, x6, x7] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7
    exact h x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6 h7
  · intro h x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6 h7
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7

@[simp] theorem eval_nestedFunction7
    {φ : Semiformula L ξ 8} {p1 p2 p3 p4 p5 p6 p7 : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![p1, p2, p3, p4, p5, p6, p7]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval ![z, x1, x2, x3, x4, x5, x6, x7] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7
    exact h x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6 h7
  · intro h x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6 h7
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7

@[simp] theorem eval_nestedRelation8
    {φ : Semiformula L ξ 8} {p1 p2 p3 p4 p5 p6 p7 p8 : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![p1, p2, p3, p4, p5, p6, p7, p8]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      Eval ![x1, x2, x3, x4, x5, x6, x7, x8] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7 x8, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval (x8 :> e) f p8 → Eval ![x1, x2, x3, x4, x5, x6, x7, x8] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      Eval ![x1, x2, x3, x4, x5, x6, x7, x8] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8
    exact h x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8
  · intro h x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8

@[simp] theorem eval_nestedFunction8
    {φ : Semiformula L ξ 9} {p1 p2 p3 p4 p5 p6 p7 p8 : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![p1, p2, p3, p4, p5, p6, p7, p8]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7 x8, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval (x8 :> e) f p8 → Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8
    exact h x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8
  · intro h x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8

@[simp] theorem eval_nestedRelation9
    {φ : Semiformula L ξ 9} {p1 p2 p3 p4 p5 p6 p7 p8 p9 : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![p1, p2, p3, p4, p5, p6, p7, p8, p9]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      ∀ x9, Eval (x9 :> e) f p9 →
      Eval ![x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7 x8 x9, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval (x8 :> e) f p8 → Eval (x9 :> e) f p9 → Eval ![x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      ∀ x9, Eval (x9 :> e) f p9 →
      Eval ![x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8 x9 h9
    exact h x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · intro h x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8 x9 h9

@[simp] theorem eval_nestedFunction9
    {φ : Semiformula L ξ 10} {p1 p2 p3 p4 p5 p6 p7 p8 p9 : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![p1, p2, p3, p4, p5, p6, p7, p8, p9]) ↔ ∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      ∀ x9, Eval (x9 :> e) f p9 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ := by
  suffices (∀ x1 x2 x3 x4 x5 x6 x7 x8 x9, Eval (x1 :> e) f p1 → Eval (x2 :> e) f p2 → Eval (x3 :> e) f p3 → Eval (x4 :> e) f p4 → Eval (x5 :> e) f p5 → Eval (x6 :> e) f p6 → Eval (x7 :> e) f p7 → Eval (x8 :> e) f p8 → Eval (x9 :> e) f p9 → Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ) ↔ (∀ x1, Eval (x1 :> e) f p1 →
      ∀ x2, Eval (x2 :> e) f p2 →
      ∀ x3, Eval (x3 :> e) f p3 →
      ∀ x4, Eval (x4 :> e) f p4 →
      ∀ x5, Eval (x5 :> e) f p5 →
      ∀ x6, Eval (x6 :> e) f p6 →
      ∀ x7, Eval (x7 :> e) f p7 →
      ∀ x8, Eval (x8 :> e) f p8 →
      ∀ x9, Eval (x9 :> e) f p9 →
      Eval ![z, x1, x2, x3, x4, x5, x6, x7, x8, x9] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8 x9 h9
    exact h x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · intro h x1 x2 x3 x4 x5 x6 x7 x8 x9 h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact h x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6 x7 h7 x8 h8 x9 h9

end ZFVP
