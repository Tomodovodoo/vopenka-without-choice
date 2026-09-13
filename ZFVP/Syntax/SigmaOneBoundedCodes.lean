import ZFVP.Syntax.BoundedCertificateDefinition

/-! Bounded formula-code recognition has a parameter-free Sigma-one definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSyntaxWitnessFormula : SetTheorySemisentence 3 :=
  “U n φ. !codingSupportFormula U ∧ n ∈ U ∧ φ ∈ U ∧
    ∃ O ∈ U, !boundedOmegaFormula O ∧ ∃ s ∈ U, ∃ m ∈ O,
      !boundedCertificateFormula U O s m ∧ !boundedPreviousCodeFormula U s m n φ”

def sigmaOneBoundedCodeFormula : SetTheorySemisentence 2 := .exs boundedSyntaxWitnessFormula

theorem boundedSyntaxWitnessFormula_bounded : IsBoundedSetFormula boundedSyntaxWitnessFormula :=
  .and (codingSupportFormula_bounded.subst _) (.and (.rel _ _) (.and (.rel _ _)
    (.exs (.bvar 0) (.and (boundedOmegaFormula_bounded.subst _)
      (.exs (.bvar 1) (.exs (.bvar 1) (.and (boundedCertificateFormula_bounded.subst _)
        (boundedPreviousCodeFormula_bounded.subst _))))))))

theorem sigmaOneBoundedCodeFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneBoundedCodeFormula :=
  .exs (.bounded boundedSyntaxWitnessFormula_bounded)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSyntaxWitnessFormula (U n φ : V) :
    boundedSyntaxWitnessFormula.Evalb ![U, n, φ] ↔
      IsCodingSupport U ∧ n ∈ U ∧ φ ∈ U ∧
        ∃ s ∈ U, IsBoundedCertificate s ∧ ⟨n, φ⟩ₖ ∈ range s := by
  simp [boundedSyntaxWitnessFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro hU
  let := hU
  intro hn hφ
  rw [and_iff_right hU.omega_mem]
  refine exists_congr fun s ↦ and_congr_right fun hs ↦ ?_
  constructor
  · rintro ⟨m, hm, hc, hp⟩
    obtain ⟨hc, hd⟩ := (boundedCertificateFormula_iff hs hm).mp hc
    have : IsFunction s := hc.1
    have hp' := (eval_boundedPreviousCodeFormula s m hn hφ).mp hp
    rw [← hd] at hp'
    exact ⟨hc, by simpa only [IsFunction.restrict_eq_self s (domain s) (fun _ h ↦ h)] using hp'⟩
  · rintro ⟨hc, hp⟩
    have : IsFunction s := hc.1
    refine ⟨domain s, hc.2.1, (boundedCertificateFormula_iff hs hc.2.1).mpr ⟨hc, rfl⟩, ?_⟩
    apply (eval_boundedPreviousCodeFormula s (domain s) hn hφ).mpr
    simpa only [IsFunction.restrict_eq_self s (domain s) (fun _ h ↦ h)] using hp

theorem eval_sigmaOneBoundedCodeFormula (n φ : V) :
    sigmaOneBoundedCodeFormula.Evalb ![n, φ] ↔ IsBoundedFormulaCode n φ := by
  change (∃ U : V, boundedSyntaxWitnessFormula.Evalb ![U, n, φ]) ↔ _
  simp only [eval_boundedSyntaxWitnessFormula]
  constructor
  · rintro ⟨U, _, _, _, s, _, hc, hp⟩
    exact (isBoundedFormulaCode_iff_certificate n φ).mpr ⟨s, hc, hp⟩
  · intro h
    obtain ⟨s, hc, hp⟩ := (isBoundedFormulaCode_iff_certificate n φ).mp h
    obtain ⟨U, hU, hX⟩ := codingSupport_containing ⟨n, ⟨φ, s⟩ₖ⟩ₖ
    let := hU
    obtain ⟨hn, hpair⟩ := kpair_components_mem_transitive hX
    obtain ⟨hφ, hs⟩ := kpair_components_mem_transitive hpair
    exact ⟨U, hU, hn, hφ, s, hs, hc, hp⟩

instance sigmaOneBoundedCodeFormula_defined :
    ℒₛₑₜ-relation[V] IsBoundedFormulaCode via sigmaOneBoundedCodeFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change sigmaOneBoundedCodeFormula.Evalb v ↔ IsBoundedFormulaCode (v 0) (v 1)
    rw [← hv]
    exact eval_sigmaOneBoundedCodeFormula (v 0) (v 1)⟩

end ZFVP
