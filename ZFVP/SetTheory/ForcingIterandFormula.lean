import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingPreorderTripleFormula : SetTheorySemisentence 3 :=
  forcingPreorderFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))

def forcingIterandFormula : SetTheorySemisentence 5 :=
  f“P R Q S t. !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !forcingNameFormula P t ∧
    (∀ p ∈ P, !(tripleForcingTruthFormula forcingPreorderTripleFormula) p P R Q S t) ∧
    (∀ p ∈ P, !(tripleForcingTruthFormula forcingTopFormula) p P R Q S t)”

def quadrupleTupleFormula : SetTheorySemisentence 5 :=
  f“b w x y z. b = !assignmentPrependFormula (!(numeralFormula 3))
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) z) y) x) w”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingPreorderTripleTruth_defined :
    Defined (fun v : Fin 6 → V ↦ v 0 ∈ forcingFormula (v 1) (v 2)
      forcingPreorderFormula (standardTuple ![v 3, v 4]))
      (tripleForcingTruthFormula forcingPreorderTripleFormula) := ⟨fun v ↦ by
  have he := (tripleForcingTruthFormula_defined forcingPreorderTripleFormula).iff v
  rw [forcingPreorderTripleFormula, forcingFormula_rename] at he
  have hv : (fun i : Fin 2 ↦ (![v 3, v 4, v 5] : Fin 3 → V) (![0, 1] i)) = ![v 3, v 4] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at he
  exact he⟩

instance forcingIterandFormula_defined :
    Defined (fun v : Fin 5 → V ↦ IsForcingIterand (v 0) (v 1) (v 2) (v 3) (v 4))
      forcingIterandFormula := ⟨fun v ↦ by
  simp [forcingIterandFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ]
  constructor
  · rintro ⟨hQ, hS, ht, hpre, htop⟩
    exact ⟨hQ, hS, ht, fun p hp ↦ hpre p hp _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl,
      fun p hp ↦ htop p hp _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl⟩
  · intro h
    refine ⟨h.posetName, h.orderName, h.topName, ?_, ?_⟩
    · intro p hp a b c d e f ha hb hc hd he hf
      subst a b c d e f
      exact h.preorder p hp
    · intro p hp a b c d e f ha hb hc hd he hf
      subst a b c d e f
      exact h.top p hp⟩

instance quadrupleTupleFormula_defined :
    ℒₛₑₜ-function₄[V] (fun w x y z ↦ standardTuple ![w, x, y, z]) via quadrupleTupleFormula :=
  ⟨fun v ↦ by simp [quadrupleTupleFormula, standardTuple]⟩

end ZFVP
