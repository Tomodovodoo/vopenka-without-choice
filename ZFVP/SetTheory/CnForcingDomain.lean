import ZFVP.Syntax.SigmaOneInternalForcing
import ZFVP.SetTheory.ForcingNameFamily
import ZFVP.SetTheory.DeltaOneBoundedTruth
import ZFVP.SetTheory.CnSigmaClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingDomainMatrix : SetTheorySemisentence 7 :=
  “D P R n φ b p. !boundedNameFamilyFormula P D ∧ !boundedNonemptyFormula D ∧
    !boundedFunctionFormula b n D ∧ !sigmaOneInternalForcingFormula P R D n φ b p”

theorem sigmaOneForcingDomainMatrix_sigmaOne : IsSigmaFormula 1 sigmaOneForcingDomainMatrix := by
  unfold sigmaOneForcingDomainMatrix
  exact .and (.bounded (boundedNameFamilyFormula_bounded.subst _))
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
      (.and (.bounded (boundedFunctionFormula_bounded.subst _))
        (sigmaOneInternalForcingFormula_sigmaOne.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneForcingDomainMatrix {D P R n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hp : p ∈ P) :
    sigmaOneForcingDomainMatrix.Evalb ![D, P, R, n, φ, b, p] ↔
      IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
        InternalForces P R D n φ b p := by
  simp only [sigmaOneForcingDomainMatrix]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro _ _ hb
  exact eval_sigmaOneInternalForcingFormula hφ hb hp

theorem Cn.forcingDomain_family {δ P R n φ b p : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hb : b ∈ hierarchy δ)
    (hφ : IsMembershipFormulaCode n φ) (hp : p ∈ P)
    (hex : ∃ D, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
      InternalForces P R D n φ b p) :
    ∃ D ∈ hierarchy δ, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
      InternalForces P R D n φ b p := by
  let := hδ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  have hnu : n ∈ hierarchy δ := IsCodingSupport.natural_mem hφ.context
  have hφu : φ ∈ hierarchy δ := membershipFormulaCode_formula_mem_support hφ
  have hpu := (hierarchy_transitive δ).mem_trans hp hP
  have he : (Semiformula.exs sigmaOneForcingDomainMatrix).Evalb ![P, R, n, φ, b, p] := by
    obtain ⟨D, hD⟩ := hex
    exact ⟨D, (eval_sigmaOneForcingDomainMatrix hφ hp).mpr hD⟩
  obtain ⟨D, hD, hmat⟩ := hδ.sigmaOne_witness sigmaOneForcingDomainMatrix_sigmaOne ![P, R, n, φ, b, p]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hR, hnu, hφu, hb, hpu]) he
  exact ⟨D, hD, (eval_sigmaOneForcingDomainMatrix hφ hp).mp hmat⟩

end ZFVP
