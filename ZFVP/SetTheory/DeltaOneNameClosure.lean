import ZFVP.SetTheory.BoundedNameClosure

/-! Sigma_1 and Pi_1 definitions of the full internal subname closure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneNameClosureFormula : SetTheorySemisentence 2 :=
  “C τ. ∃ T, ∃ w, ∃ f, !IsTransitive.dfn T ∧ !boundedOmegaFormula w ∧
    !boundedSubnameIterationFormula T w f τ ∧ !boundedIterationUnionFormula C T w f”

def sigmaOneNonNameClosureFormula : SetTheorySemisentence 2 :=
  “C τ. ∃ D, !sigmaOneNameClosureFormula D τ ∧ D ≠ C”

def piOneNameClosureFormula : SetTheorySemisentence 2 := ∼sigmaOneNonNameClosureFormula

theorem sigmaOneNameClosureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNameClosureFormula :=
  .exs (.exs (.exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (boundedOmegaFormula_bounded.subst _))
      (.and (.bounded (boundedSubnameIterationFormula_bounded.subst _))
        (.bounded (boundedIterationUnionFormula_bounded.subst _)))))))

theorem sigmaOneNonNameClosureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNonNameClosureFormula :=
  .exs (.and (sigmaOneNameClosureFormula_sigmaOne.subst _) (.bounded (.nrel _ _)))

theorem piOneNameClosureFormula_piOne : IsPiFormula 1 piOneNameClosureFormula :=
  sigmaOneNonNameClosureFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneNameClosureFormula (C τ : V) :
    sigmaOneNameClosureFormula.Evalb ![C, τ] ↔ C = nameClosure τ := by
  have hev : sigmaOneNameClosureFormula.Evalb ![C, τ] ↔ ∃ T f : V, IsTransitive T ∧
      boundedSubnameIterationFormula.Evalb ![T, ω, f, τ] ∧
        boundedIterationUnionFormula.Evalb ![C, T, ω, f] := by
    simp [sigmaOneNameClosureFormula]
  rw [hev]
  constructor
  · rintro ⟨T, f, hT, hiter, hC⟩
    let := hT
    obtain ⟨hf, rfl⟩ := (eval_boundedSubnameIterationFormula f τ).mp hiter
    exact ((eval_boundedIterationUnionFormula hf C).mp hC).trans (nameClosure_eq_iteration τ).symm
  · rintro rfl
    let f := subnameIterationGraph τ
    let T := transitiveClosure (range f)
    have hT : IsTransitive T := transitiveClosure_transitive _
    let := hT
    have hfr : f ∈ (range f) ^ (ω : V) := by
      rw [← domain_subnameIterationGraph τ]
      exact IsFunction.mem_function f
    have hf : f ∈ T ^ (ω : V) :=
      mem_function_of_mem_function_of_subset hfr (subset_transitiveClosure (range f))
    exact ⟨T, f, hT, (eval_boundedSubnameIterationFormula f τ).mpr ⟨hf, rfl⟩,
      (eval_boundedIterationUnionFormula hf _).mpr (nameClosure_eq_iteration τ)⟩

theorem eval_sigmaOneNonNameClosureFormula (C τ : V) :
    sigmaOneNonNameClosureFormula.Evalb ![C, τ] ↔ C ≠ nameClosure τ := by
  simp [sigmaOneNonNameClosureFormula, eval_sigmaOneNameClosureFormula, eq_comm]

theorem eval_piOneNameClosureFormula (C τ : V) :
    piOneNameClosureFormula.Evalb ![C, τ] ↔ C = nameClosure τ := by
  simp [piOneNameClosureFormula, eval_sigmaOneNonNameClosureFormula]

instance sigmaOneNameClosureFormula_defined :
    ℒₛₑₜ-function₁[V] nameClosure via sigmaOneNameClosureFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change sigmaOneNameClosureFormula.Evalb v ↔ v 0 = nameClosure (v 1)
    rw [← hv]
    exact eval_sigmaOneNameClosureFormula (v 0) (v 1)⟩

instance piOneNameClosureFormula_defined :
    ℒₛₑₜ-function₁[V] nameClosure via piOneNameClosureFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change piOneNameClosureFormula.Evalb v ↔ v 0 = nameClosure (v 1)
    rw [← hv]
    exact eval_piOneNameClosureFormula (v 0) (v 1)⟩

end ZFVP
