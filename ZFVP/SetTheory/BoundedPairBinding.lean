import ZFVP.SetTheory.BoundedCodingPrimitives

/-! Components of a Kuratowski pair can be bound using only membership bounds. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPairBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 2)) : SetTheorySemisentence n :=
  boundedSetExs t (boundedSetExs (.bvar 0)
    (boundedSetExs (Rew.bShift (Rew.bShift t)) (boundedSetExs (.bvar 0)
      ((boundedKpairFormula.subst ![Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift t))), .bvar 2, .bvar 0]).and
        (φ.subst (.bvar 2 :> .bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ))))))

theorem boundedPairBind_levy {n k : ℕ} {p : LevyPolarity}
    (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 2)}
    (hφ : IsLevyFormula p k φ) : IsLevyFormula p k (boundedPairBind t φ) :=
  .boundedExs t (.boundedExs (.bvar 0) (.boundedExs _ (.boundedExs (.bvar 0)
    (.and (.bounded (boundedKpairFormula_bounded.subst _)) (hφ.subst _)))))

theorem boundedPairBind_bounded {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 2)} (hφ : IsBoundedSetFormula φ) :
    IsBoundedSetFormula (boundedPairBind t φ) :=
  .exs t (.exs (.bvar 0) (.exs _ (.exs (.bvar 0)
    (.and (boundedKpairFormula_bounded.subst _) (hφ.subst _)))))

def boundedQuadrupleBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 4)) : SetTheorySemisentence n :=
  boundedPairBind t (boundedPairBind (.bvar 1) (boundedPairBind (.bvar 1)
    (φ.subst (.bvar 4 :> .bvar 2 :> .bvar 0 :> .bvar 1 :>
      fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ))))

theorem boundedQuadrupleBind_levy {n k : ℕ} {p : LevyPolarity}
    (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 4)}
    (hφ : IsLevyFormula p k φ) : IsLevyFormula p k (boundedQuadrupleBind t φ) :=
  boundedPairBind_levy t (boundedPairBind_levy _ (boundedPairBind_levy _ (hφ.subst _)))

theorem boundedQuadrupleBind_bounded {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 4)} (hφ : IsBoundedSetFormula φ) :
    IsBoundedSetFormula (boundedQuadrupleBind t φ) :=
  boundedPairBind_bounded t (boundedPairBind_bounded _ (boundedPairBind_bounded _ (hφ.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_boundedPairBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 2)) (v : Fin n → V) :
    (boundedPairBind t φ).Evalb v ↔
      ∃ a b : V, t.val v Empty.elim = ⟨a, b⟩ₖ ∧ φ.Evalb (a :> b :> v) := by
  simp [boundedPairBind, eval_boundedSetExs, eval_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨s, _, a, _, d, _, b, _, he, hφ⟩
    exact ⟨a, b, he, hφ⟩
  · rintro ⟨a, b, he, hφ⟩
    refine ⟨{a}, ?_, a, by simp, {a, b}, ?_, b, by simp, he, hφ⟩ <;> simp [he, kpair]

theorem eval_boundedQuadrupleBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 4)) (v : Fin n → V) :
    (boundedQuadrupleBind t φ).Evalb v ↔
      ∃ a b c d : V, t.val v Empty.elim = ⟨a, ⟨b, ⟨c, d⟩ₖ⟩ₖ⟩ₖ ∧ φ.Evalb (a :> b :> c :> d :> v) := by
  simp [boundedQuadrupleBind, eval_boundedPairBind, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def]

end ZFVP
