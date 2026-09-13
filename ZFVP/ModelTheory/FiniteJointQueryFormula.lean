import ZFVP.ModelTheory.FiniteJointNamingFormula

/-! The source argument of a query remains an outer bound variable while the
finite assignment of names is existentially quantified. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type*} [SetStructure M]

def finiteJointQueryFormula {N p : ℕ} (ψ : SetTheorySemisentence N)
    (θ : SetTheorySemisentence (N + 1)) (source : Fin N → Option M)
    (slot : Fin p → Option (Fin N)) : SetTheorySemiformula M (p + 1) :=
  ∃¹^[N] (((Rew.embSubsts (fun t : Fin N ↦ #(t.addCast (p + 1)))) ▹ ψ) ⋏
    ((Rew.embSubsts (#((0 : Fin (p + 1)).addNat N) :>
      (fun t : Fin N ↦ #(t.addCast (p + 1))))) ▹ θ) ⋏
    finiteSourceNameGuard source ⋏ finiteUpperNameGuard (none :> slot))

theorem eval_finiteJointQueryFormula {N p : ℕ} (ψ : SetTheorySemisentence N)
    (θ : SetTheorySemisentence (N + 1)) (source : Fin N → Option M)
    (slot : Fin p → Option (Fin N)) (x : M) (u : Fin p → M) :
    Semiformula.Eval (x :> u) id (finiteJointQueryFormula ψ θ source slot) ↔
      ∃ a : Fin N → M, ψ.Evalb a ∧ θ.Evalb (x :> a) ∧
        (∀ t y, source t = some y → a t = y) ∧
        ∀ t s, slot t = some s → a s = u t := by
  rw [finiteJointQueryFormula, Semiformula.eval_exsItr]
  apply exists_congr
  intro a
  simp only [LogicalConnective.HomClass.map_and, eval_finiteSourceNameGuard,
    eval_finiteUpperNameGuard, Semiformula.eval_embSubsts]
  have ha : (Semiterm.val (Matrix.appendr a (x :> u)) id ∘
      (fun t : Fin N ↦ (#(t.addCast (p + 1)) : Semiterm ℒₛₑₜ M ((p + 1) + N)))) = a := by
    funext t
    simp
  have hx : (Semiterm.val (L := ℒₛₑₜ) (Matrix.appendr a (x :> u)) id ∘
      (#((0 : Fin (p + 1)).addNat N) :> (fun t : Fin N ↦ #(t.addCast (p + 1))))) = x :> a := by
    funext t
    cases t using Fin.cases <;> simp
  rw [ha, hx]
  simp [Fin.forall_fin_succ]

end ZFVP
