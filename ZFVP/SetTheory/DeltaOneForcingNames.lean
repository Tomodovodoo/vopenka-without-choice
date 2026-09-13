import ZFVP.SetTheory.DeltaOneNameClosure
import ZFVP.SetTheory.ForcingNames

/-! Forcing-name validity has uniform Sigma_1 and Pi_1 definitions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNameFamilyFormula : SetTheorySemisentence 2 :=
  “P C. ∀ σ ∈ C, ∀ z ∈ σ, ∃ u ∈ C, ∃ p ∈ P, !boundedKpairFormula z u p”

theorem boundedNameFamilyFormula_bounded : IsBoundedSetFormula boundedNameFamilyFormula :=
  .all (.bvar 1) (.all (.bvar 0) (.exs (.bvar 3) (.exs (.bvar 3)
    (boundedKpairFormula_bounded.subst _))))

def sigmaOneForcingNameFormula : SetTheorySemisentence 2 :=
  “P τ. ∃ C, !sigmaOneNameClosureFormula C τ ∧ !boundedNameFamilyFormula P C”

def sigmaOneNonForcingNameFormula : SetTheorySemisentence 2 :=
  “P τ. ∃ C, !sigmaOneNameClosureFormula C τ ∧ ¬!boundedNameFamilyFormula P C”

def piOneForcingNameFormula : SetTheorySemisentence 2 := ∼sigmaOneNonForcingNameFormula

theorem sigmaOneForcingNameFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingNameFormula :=
  .exs (.and (sigmaOneNameClosureFormula_sigmaOne.subst _) (.bounded (boundedNameFamilyFormula_bounded.subst _)))

theorem sigmaOneNonForcingNameFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNonForcingNameFormula :=
  .exs (.and (sigmaOneNameClosureFormula_sigmaOne.subst _) (.bounded (boundedNameFamilyFormula_bounded.subst _).neg))

theorem piOneForcingNameFormula_piOne : IsPiFormula 1 piOneForcingNameFormula :=
  sigmaOneNonForcingNameFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedNameFamilyFormula (P τ : V) :
    boundedNameFamilyFormula.Evalb ![P, nameClosure τ] ↔ IsForcingName P τ := by
  simp [boundedNameFamilyFormula, IsForcingName]
  constructor
  · intro h σ hσ z hz
    obtain ⟨u, _, p, hp, he⟩ := h σ hσ z hz
    exact ⟨u, p, hp, he⟩
  · intro h σ hσ z hz
    obtain ⟨u, p, hp, he⟩ := h σ hσ z hz
    exact ⟨u, nameClosure_closed τ σ hσ u (mem_domain_of_kpair_mem (he ▸ hz)), p, hp, he⟩

theorem eval_sigmaOneForcingNameFormula (P τ : V) :
    sigmaOneForcingNameFormula.Evalb ![P, τ] ↔ IsForcingName P τ := by
  simp [sigmaOneForcingNameFormula, eval_boundedNameFamilyFormula]

theorem eval_sigmaOneNonForcingNameFormula (P τ : V) :
    sigmaOneNonForcingNameFormula.Evalb ![P, τ] ↔ ¬IsForcingName P τ := by
  simp [sigmaOneNonForcingNameFormula, eval_boundedNameFamilyFormula]

theorem eval_piOneForcingNameFormula (P τ : V) :
    piOneForcingNameFormula.Evalb ![P, τ] ↔ IsForcingName P τ := by
  simp [piOneForcingNameFormula, eval_sigmaOneNonForcingNameFormula]

instance sigmaOneForcingNameFormula_defined : ℒₛₑₜ-relation[V] IsForcingName via sigmaOneForcingNameFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change sigmaOneForcingNameFormula.Evalb v ↔ IsForcingName (v 0) (v 1)
    rw [← hv]
    exact eval_sigmaOneForcingNameFormula (v 0) (v 1)⟩

instance piOneForcingNameFormula_defined : ℒₛₑₜ-relation[V] IsForcingName via piOneForcingNameFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change piOneForcingNameFormula.Evalb v ↔ IsForcingName (v 0) (v 1)
    rw [← hv]
    exact eval_piOneForcingNameFormula (v 0) (v 1)⟩

end ZFVP
