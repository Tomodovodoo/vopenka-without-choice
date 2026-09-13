import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedProduct
import ZFVP.SetTheory.BoundedIdentity
import ZFVP.SetTheory.ForcingLiftExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPairSecondValueFormula : SetTheorySemisentence 2 :=
  “y a. ∃ u ∈ a, ∃ x ∈ u, !boundedKpairFormula a x y”

theorem boundedPairSecondValueFormula_bounded : IsBoundedSetFormula boundedPairSecondValueFormula :=
  .exs (.bvar 1) (.exs (.bvar 0) (boundedKpairFormula_bounded.subst _))

def sigmaOneIdentityLiftFormula : SetTheorySemisentence 2 :=
  “I Q. ∃ A, !boundedProductFormula A Q Q ∧ !(graphAssemblyFormula boundedPairSecondValueFormula) I A”

def piOneIdentityLiftFormula : SetTheorySemisentence 2 :=
  “I Q. ∀ A, !boundedProductFormula A Q Q → !(graphAssemblyFormula boundedPairSecondValueFormula) I A”

theorem sigmaOneIdentityLiftFormula_sigmaOne : IsSigmaFormula 1 sigmaOneIdentityLiftFormula :=
  .exs (.bounded (.and (boundedProductFormula_bounded.subst _)
    ((graphAssemblyFormula_bounded boundedPairSecondValueFormula_bounded).subst _)))

theorem piOneIdentityLiftFormula_piOne : IsPiFormula 1 piOneIdentityLiftFormula :=
  .all (.bounded (.or (boundedProductFormula_bounded.subst _).neg
    ((graphAssemblyFormula_bounded boundedPairSecondValueFormula_bounded).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedPairSecondValueFormula_pair (y i j : V) :
    boundedPairSecondValueFormula.Evalb ![y, ⟨i, j⟩ₖ] ↔ y = kpair.π₂ ⟨i, j⟩ₖ := by
  have hi : ∃ u ∈ ⟨i, j⟩ₖ, i ∈ u :=
    ⟨doubleton i j, by simp [kpair, pair_eq_doubleton], by simp⟩
  simp [boundedPairSecondValueFormula, eq_comm]
  constructor
  · rintro ⟨u, _, _, hy⟩
    exact hy
  · intro hy
    obtain ⟨u, hu, hiu⟩ := hi
    exact ⟨u, hu, hiu, hy⟩

theorem eval_identityLiftGraphAssembly (I Q : V) :
    (graphAssemblyFormula boundedPairSecondValueFormula).Evalb ![I, Q ×ˢ Q] ↔
      I = forcingIdentityLift Q := by
  apply eval_graphAssemblyFormula boundedPairSecondValueFormula I (Q ×ˢ Q) ![]
    kpair.π₂ (by definability)
  intro a ha y
  obtain ⟨i, _, j, _, rfl⟩ := mem_prod_iff.mp ha
  exact eval_boundedPairSecondValueFormula_pair y i j

theorem eval_sigmaOneIdentityLiftFormula (I Q : V) :
    sigmaOneIdentityLiftFormula.Evalb ![I, Q] ↔ I = forcingIdentityLift Q := by
  have he : sigmaOneIdentityLiftFormula.Evalb ![I, Q] ↔
      (graphAssemblyFormula boundedPairSecondValueFormula).Evalb ![I, Q ×ˢ Q] := by
    simp [sigmaOneIdentityLiftFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_identityLiftGraphAssembly I Q)

theorem eval_piOneIdentityLiftFormula (I Q : V) :
    piOneIdentityLiftFormula.Evalb ![I, Q] ↔ I = forcingIdentityLift Q := by
  have he : piOneIdentityLiftFormula.Evalb ![I, Q] ↔
      (graphAssemblyFormula boundedPairSecondValueFormula).Evalb ![I, Q ×ˢ Q] := by
    simp [piOneIdentityLiftFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_identityLiftGraphAssembly I Q)

instance sigmaOneIdentityLiftFormula_defined : ℒₛₑₜ-function₁[V] forcingIdentityLift via sigmaOneIdentityLiftFormula :=
  ⟨fun v ↦ by
    change sigmaOneIdentityLiftFormula.Evalb v ↔ v 0 = forcingIdentityLift (v 1)
    have hv : v = ![v 0, v 1] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneIdentityLiftFormula.Evalb w) hv)).trans
      (eval_sigmaOneIdentityLiftFormula (v 0) (v 1))⟩

instance piOneIdentityLiftFormula_defined : ℒₛₑₜ-function₁[V] forcingIdentityLift via piOneIdentityLiftFormula :=
  ⟨fun v ↦ by
    change piOneIdentityLiftFormula.Evalb v ↔ v 0 = forcingIdentityLift (v 1)
    have hv : v = ![v 0, v 1] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneIdentityLiftFormula.Evalb w) hv)).trans
      (eval_piOneIdentityLiftFormula (v 0) (v 1))⟩

end ZFVP
