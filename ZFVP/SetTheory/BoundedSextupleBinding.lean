import ZFVP.SetTheory.BoundedPairBinding

/-! Bounded extraction of six components from a nested Kuratowski tuple. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSextupleBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 6)) : SetTheorySemisentence n :=
  boundedPairBind t (boundedPairBind (.bvar 1) (boundedQuadrupleBind (.bvar 1)
    (φ.subst (.bvar 6 :> .bvar 4 :> .bvar 0 :> .bvar 1 :> .bvar 2 :> .bvar 3 :>
      fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ.succ.succ))))

theorem boundedSextupleBind_levy {n k : ℕ} {p : LevyPolarity}
    (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 6)}
    (hφ : IsLevyFormula p k φ) : IsLevyFormula p k (boundedSextupleBind t φ) :=
  boundedPairBind_levy t (boundedPairBind_levy _ (boundedQuadrupleBind_levy _ (hφ.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSextupleBind {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 6)) (v : Fin n → V) :
    (boundedSextupleBind t φ).Evalb v ↔ ∃ a b c d e f : V,
      t.val v Empty.elim = ⟨a, ⟨b, ⟨c, ⟨d, ⟨e, f⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∧
        φ.Evalb (a :> b :> c :> d :> e :> f :> v) := by
  simp [boundedSextupleBind, eval_boundedPairBind, eval_boundedQuadrupleBind,
    Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def]

end ZFVP
