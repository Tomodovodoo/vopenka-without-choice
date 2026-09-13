import ZFVP.ModelTheory.DeltaOneSuccessorCode
import ZFVP.ModelTheory.SigmaThreeSaturatedPrefixNames
import ZFVP.SetTheory.SigmaThreeLeastPrefixCutoff
import ZFVP.ModelTheory.WoodinIterationSuccessor

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def selectedWoodinSuccessorCertificate (Λ : SetTheorySemisentence 5)
    (Ξ Ω : SetTheorySemisentence 6) (φ : BoundedFormulaTree 3) : SetTheorySemisentence 4 :=
  “z k s K. ∃ Pt, !sigmaOneForcingCodePFormula Pt s ∧
    ∃ Rt, !sigmaOneForcingCodeRFormula Rt s ∧
    ∃ ot, !sigmaOneForcingCodetFormula ot s ∧
    ∃ P, !boundedValueFormula P Pt k ∧
    ∃ R, !boundedValueFormula R Rt k ∧
    ∃ o, !boundedValueFormula o ot k ∧
    ∃ κ, !boundedValueFormula κ K k ∧
    ∃ δ, !Λ P R o κ δ ∧
    ∃ Q, !Ξ Q P R o κ δ ∧
    ∃ S, !Ω S P R o κ δ ∧
    ∃ u, !boundedEmptyFormula u ∧
    !(sigmaOneSuccessorCodeCertificate φ) z k s Q S u”

theorem selectedWoodinSuccessorCertificate_sigmaThree {Λ : SetTheorySemisentence 5}
    {Ξ Ω : SetTheorySemisentence 6} (hΛ : IsSigmaFormula 3 Λ)
    (hΞ : IsSigmaFormula 3 Ξ) (hΩ : IsSigmaFormula 3 Ω) (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 3 (selectedWoodinSuccessorCertificate Λ Ξ Ω φ) :=
  .exs (.and ((sigmaOneForcingCodePFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and ((sigmaOneForcingCodeRFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and ((sigmaOneForcingCodetFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (hΛ.subst _)
    (.exs (.and (hΞ.subst _)
    (.exs (.and (hΩ.subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    ((sigmaOneSuccessorCodeCertificate_sigmaOne φ).mono (by omega) |>.subst _))))))))))))))))))))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_selectedWoodinSuccessorCertificate
    (Λ : SetTheorySemisentence 5) (Ξ Ω : SetTheorySemisentence 6)
    (φ : BoundedFormulaTree 3) (hφ : φ.formula = boundedPairMemberFormula)
    (k s K : V)
    (hΛ : ∀ δ : V, Λ.Evalb ![(forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k, δ] ↔ δ = woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k))
    (hΞ : ∀ Q : V, Ξ.Evalb ![Q, (forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k, woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)] ↔
      Q = saturatedWoodinPrefixPosetName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k) (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)))
    (hΩ : ∀ S : V, Ω.Evalb ![S, (forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k, woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)] ↔
      S = saturatedWoodinPrefixOrderName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k) (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)))
    (hR : IsForcingPreorder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k))
    (hI : IsForcingIterand ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      (saturatedWoodinPrefixPosetName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k) (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)))
      (saturatedWoodinPrefixOrderName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k) (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k))) ∅) (z : V) :
    (selectedWoodinSuccessorCertificate Λ Ξ Ω φ).Evalb ![z, k, s, K] ↔
      z = woodinIterationSuccessor k s K := by
  have he := eval_sigmaOneSuccessorCodeCertificate φ hφ hR hI
  simp only [Semiformula.Evalb] at hΛ hΞ hΩ he
  simp [selectedWoodinSuccessorCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΛ, hΞ, hΩ, he, woodinIterationSuccessor]

theorem woodinIterationSuccessor_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ k s K : V,
        let P := (forcingCodeP s) ‘ k;
        let R := (forcingCodeR s) ‘ k;
        let o := (forcingCodet s) ‘ k;
        let κ := K ‘ k;
        IsForcingPreorder P R → IsForcingTop P R o → (∅ : V) ∈ κ →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ])) →
        (∃ δ, IsWoodinPrefixCutoff P R o κ δ) →
        P ∈ hierarchy (woodinPrefixCutoff P R o κ) → ∀ z,
          (Λ.Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := leastWoodinPrefixCutoff_deltaThree_uniform.{u}
  obtain ⟨Ξ, hΞ, heΞ⟩ := saturatedWoodinPrefixPosetName_sigmaThree_uniform.{u}
  obtain ⟨Ω, hΩ, heΩ⟩ := saturatedWoodinPrefixOrderName_sigmaThree_uniform.{u}
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  refine ⟨selectedWoodinSuccessorCertificate Λ Ξ Ω φ,
    selectedWoodinSuccessorCertificate_sigmaThree (hΛ .sigma) hΞ hΩ φ, ?_⟩
  intro V _ _ _ k s K
  dsimp only
  intro hR ht hk hreg hex hP z
  obtain ⟨δ, hδ⟩ := hex
  have hleast := woodinPrefixCutoff_spec hδ
  apply eval_selectedWoodinSuccessorCertificate Λ Ξ Ω φ hφ k s K
  · intro d
    exact (heΛ V _ _ _ _ d hR ht hk).trans
      (woodinPrefixCutoff_eq_iff_least_of_exists ⟨δ, hδ⟩).symm
  · intro Q
    exact heΞ V Q _ _ _ _ _ hR ht hleast.1
  · intro S
    exact heΩ V S _ _ _ _ _ hR ht hleast.1
  · exact hR
  · exact saturatedWoodinPrefix_iterand_of_cutoff hR ht hreg hleast.2.1 hP

def woodinSuccessorPiCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z k s K. ∀ w, !Λ w k s K → z = w”

theorem woodinSuccessorPiCertificate_piThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (woodinSuccessorPiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

theorem eval_woodinSuccessorPiCertificate (Λ : SetTheorySemisentence 4) (z k s K : V)
    (he : ∀ w : V, Λ.Evalb ![w, k, s, K] ↔ w = woodinIterationSuccessor k s K) :
    (woodinSuccessorPiCertificate Λ).Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K := by
  simp only [Semiformula.Evalb] at he
  simp [woodinSuccessorPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinIterationSuccessor_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ k s K : V,
        let P := (forcingCodeP s) ‘ k;
        let R := (forcingCodeR s) ‘ k;
        let o := (forcingCodet s) ‘ k;
        let κ := K ‘ k;
        IsForcingPreorder P R → IsForcingTop P R o → (∅ : V) ∈ κ →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ])) →
        (∃ δ, IsWoodinPrefixCutoff P R o κ δ) →
        P ∈ hierarchy (woodinPrefixCutoff P R o κ) → ∀ z,
          (Λ.Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K) ∧
          (Ξ.Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinIterationSuccessor_sigmaThree_uniform.{u}
  refine ⟨Λ, woodinSuccessorPiCertificate Λ, hΛ, woodinSuccessorPiCertificate_piThree hΛ, ?_⟩
  intro V _ _ _ k s K
  dsimp only
  intro hR ht hk hreg hex hP z
  exact ⟨he V k s K hR ht hk hreg hex hP z,
    eval_woodinSuccessorPiCertificate Λ z k s K (he V k s K hR ht hk hreg hex hP)⟩

end ZFVP
