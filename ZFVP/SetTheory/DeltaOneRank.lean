import ZFVP.SetTheory.BoundedRankTables
import ZFVP.SetTheory.LevySubstitution

/-! Sigma-one and Pi-one definitions of the rank function. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneRankFormula : SetTheorySemisentence 2 :=
  “α x. ∃ T, !IsTransitive.dfn T ∧ x ∈ T ∧ ∃ R, ∃ f,
    !boundedRankTableFormula T R f ∧ !boundedPairMemberFormula f x α”

def sigmaOneNonRankFormula : SetTheorySemisentence 2 :=
  “α x. ∃ β, !sigmaOneRankFormula β x ∧ β ≠ α”

def piOneRankFormula : SetTheorySemisentence 2 := ∼sigmaOneNonRankFormula

theorem sigmaOneRankFormula_sigmaOne : IsSigmaFormula 1 sigmaOneRankFormula :=
  .exs (.and (.bounded (isTransitiveFormula_bounded.subst _)) (.and (.bounded (.rel _ _))
    (.exs (.exs (.and (.bounded (boundedRankTableFormula_bounded.subst _))
      (.bounded (boundedPairMemberFormula_bounded.subst _)))))))

theorem sigmaOneNonRankFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNonRankFormula :=
  .exs (.and (sigmaOneRankFormula_sigmaOne.subst _) (.bounded (.nrel _ _)))

theorem piOneRankFormula_piOne : IsPiFormula 1 piOneRankFormula := sigmaOneNonRankFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneRankFormula (α x : V) : sigmaOneRankFormula.Evalb ![α, x] ↔ α = rank x := by
  simp [sigmaOneRankFormula]
  constructor
  · rintro ⟨T, hT, hx, R, f, hf, hp⟩
    let := hT
    have hf' := (eval_boundedRankTableFormula R f).mp hf
    let := IsFunction.of_mem hf'.1
    exact (value_eq_of_kpair_mem hp).symm.trans (rankTable_correct hf' x hx)
  · intro hα
    obtain ⟨T, hT, hx⟩ := codingSupport_containing x
    let := hT
    obtain ⟨R, f, hf⟩ := rankTable_exists T
    let := IsFunction.of_mem hf.1
    refine ⟨T, hT.toIsTransitive, hx, R, f, (eval_boundedRankTableFormula R f).mpr hf, ?_⟩
    exact kpair_mem_iff_value.mpr ⟨by simpa only [domain_eq_of_mem_function hf.1] using hx,
      (rankTable_correct hf x hx).trans hα.symm⟩

theorem eval_sigmaOneNonRankFormula (α x : V) : sigmaOneNonRankFormula.Evalb ![α, x] ↔ α ≠ rank x := by
  simp [sigmaOneNonRankFormula, eval_sigmaOneRankFormula, eq_comm]

theorem eval_piOneRankFormula (α x : V) : piOneRankFormula.Evalb ![α, x] ↔ α = rank x := by
  simp [piOneRankFormula, eval_sigmaOneNonRankFormula]

instance sigmaOneRankFormula_defined : ℒₛₑₜ-function₁[V] rank via sigmaOneRankFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change sigmaOneRankFormula.Evalb v ↔ v 0 = rank (v 1)
    rw [← hv]
    exact eval_sigmaOneRankFormula (v 0) (v 1)⟩

instance piOneRankFormula_defined : ℒₛₑₜ-function₁[V] rank via piOneRankFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change piOneRankFormula.Evalb v ↔ v 0 = rank (v 1)
    rw [← hv]
    exact eval_piOneRankFormula (v 0) (v 1)⟩

end ZFVP
