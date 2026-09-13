import ZFVP.ModelTheory.FixedWoodinInverseCutoff
import ZFVP.ModelTheory.SigmaThreeSaturatedHartogsNames

/-! A fixed Hartogs-name graph and fixed successful cutoff selectors. Syntax is
declared before interpreted structures; semantic lemmas hold in arbitrary ZF
models. Existence is derived when specializing to the constructed sparse branch. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

noncomputable def fixedSigmaThreeHartogsNameFormula : SetTheorySemisentence 4 :=
  levyUniqueNameGraphFormula (unaryNameOutputFormula
    (fixedOrdinaryForcingFormula (deltaTwoHartogsFormula_levy .sigma) (by decide)))

theorem fixedSigmaThreeHartogsNameFormula_sigmaThree : IsSigmaFormula 3 fixedSigmaThreeHartogsNameFormula :=
  levyUniqueNameGraphFormula_sigma
    ((fixedOrdinaryForcingFormula_levy (deltaTwoHartogsFormula_levy .sigma) (by decide)).subst _)

noncomputable def fixedSigmaThreeCheckedHartogsNameFormula : SetTheorySemisentence 5 :=
  checkedHartogsNameCertificate fixedSigmaThreeHartogsNameFormula

theorem fixedSigmaThreeCheckedHartogsNameFormula_sigmaThree : IsSigmaFormula 3 fixedSigmaThreeCheckedHartogsNameFormula :=
  checkedHartogsNameCertificate_sigmaThree fixedSigmaThreeHartogsNameFormula_sigmaThree

noncomputable def fixedSigmaThreeHartogsCutoffSelectorFormula : SetTheorySemisentence 5 :=
  “δ P R one γ. ∃ τ, !fixedSigmaThreeCheckedHartogsNameFormula τ P R one γ ∧
    !fixedLeastNamedPrefixCutoffFormula P R one γ τ δ”

theorem fixedSigmaThreeHartogsCutoffSelectorFormula_sigmaThree :
    IsSigmaFormula 3 fixedSigmaThreeHartogsCutoffSelectorFormula :=
  .exs (.and (fixedSigmaThreeCheckedHartogsNameFormula_sigmaThree.subst _)
    ((fixedLeastNamedPrefixCutoffFormula_levy .sigma).subst _))

noncomputable def fixedPiThreeHartogsCutoffSelectorFormula : SetTheorySemisentence 5 :=
  “δ P R one γ. ∀ d, !fixedSigmaThreeHartogsCutoffSelectorFormula d P R one γ → δ = d”

theorem fixedPiThreeHartogsCutoffSelectorFormula_piThree :
    IsPiFormula 3 fixedPiThreeHartogsCutoffSelectorFormula :=
  .all (.or (fixedSigmaThreeHartogsCutoffSelectorFormula_sigmaThree.subst _).neg (.bounded (.rel _ _)))

universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_unaryNameOutputFormula_fixed (Ψ : SetTheorySemisentence 5) (P R τ ν p : V) :
    (unaryNameOutputFormula Ψ).Evalb ![P, R, τ, ν, p] ↔ Ψ.Evalb ![P, R, p, ν, τ] := by
  simp [unaryNameOutputFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]

private theorem eval_unaryNameCertificate_fixed (φ χ : SetTheorySemisentence 2) (Ψ : SetTheorySemisentence 5)
    (hv : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ b : Fin 2 → W, χ.Evalb b ↔ φ.Evalb b) {N P R one τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hΨ : ∀ ν : V, IsForcingName P ν → ∀ p : V,
      Ψ.Evalb ![P, R, p, ν, τ] ↔ p ∈ forcingFormula P R χ (standardTuple ![ν, τ])) :
    (levyUniqueNameGraphFormula (unaryNameOutputFormula Ψ)).Evalb ![N, P, R, τ] ↔
      N = formulaUniqueName P R φ (standardTuple ![τ]) := by
  apply eval_levyUniqueNameGraphFormula _ N P R τ (standardTuple ![τ])
    (fun b ν ↦ forcingFormula P R φ (assignmentPrepend (1 : V) b ν)) (by definability)
  intro ν hν p
  have hnames : ∀ i : Fin 2, IsForcingName P ((![ν, τ] : Fin 2 → V) i) := by
    intro i
    exact Fin.cases hν (fun j ↦ Fin.cases hτ (fun e ↦ Fin.elim0 e) j) i
  rw [eval_unaryNameOutputFormula_fixed, hΨ ν hν p]
  let v : Fin 2 → ForcingName P := fun i ↦ ⟨![ν, τ] i, hnames i⟩
  constructor
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability)
      χ (standardTuple ![ν, τ]) p h
    exact forcingFormula_entailment χ φ
      (fun W _ _ _ b ↦ (hv W b).mp) hR ht hp v h
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability)
      φ (standardTuple ![ν, τ]) p h
    exact forcingFormula_entailment φ χ
      (fun W _ _ _ b ↦ (hv W b).mpr) hR ht hp v h

theorem eval_fixedSigmaThreeHartogsNameFormula {N P R one τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ) :
    fixedSigmaThreeHartogsNameFormula.Evalb ![N, P, R, τ] ↔ N = hartogsNumberName P R τ := by
  apply eval_unaryNameCertificate_fixed hartogsNumberFormula deltaTwoHartogsFormula
    (fixedOrdinaryForcingFormula (deltaTwoHartogsFormula_levy .sigma) (by decide))
    (fun W _ _ _ b ↦ (deltaTwoHartogsFormula_defined.iff b).trans (hartogsNumberFormula_defined.iff b).symm) hR ht hτ
  intro ν hν p
  exact eval_fixedOrdinaryForcingFormula (deltaTwoHartogsFormula_levy .sigma) (by decide) hR ![ν, τ]
    (by
      intro i
      exact Fin.cases hν (fun j ↦ Fin.cases hτ (fun e ↦ Fin.elim0 e) j) i) p

theorem eval_fixedSigmaThreeCheckedHartogsNameFormula {N P R one γ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    fixedSigmaThreeCheckedHartogsNameFormula.Evalb ![N, P, R, one, γ] ↔
      N = hartogsNumberName P R (checkName one γ) := by
  have hb : fixedSigmaThreeCheckedHartogsNameFormula.Evalb ![N, P, R, one, γ] ↔
      fixedSigmaThreeHartogsNameFormula.Evalb ![N, P, R, checkName one γ] := by
    simp [fixedSigmaThreeCheckedHartogsNameFormula, checkedHartogsNameCertificate,
      eval_sigmaOneCheckNameFormula, TruthAnswer, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  exact hb.trans (eval_fixedSigmaThreeHartogsNameFormula hR ht (checkName_isName ht.1 γ))

theorem eval_fixedSigmaThreeHartogsCutoffSelectorFormula {P R one γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula
      (standardTuple ![hartogsNumberName P R (checkName one γ)]))
    (hex : ∃ η, IsWoodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) η) :
    fixedSigmaThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, one, γ] ↔
      δ = woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) := by
  have hb : fixedSigmaThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, one, γ] ↔
      ∃ τ : V, fixedSigmaThreeCheckedHartogsNameFormula.Evalb ![τ, P, R, one, γ] ∧
        fixedLeastNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] := by
    simp [fixedSigmaThreeHartogsCutoffSelectorFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [eval_fixedSigmaThreeCheckedHartogsNameFormula hR ht, exists_eq_left]
  exact (eval_fixedLeastNamedPrefixCutoffFormula hR ht (hartogsNumberName_isName _ _ _) hz).trans
    (woodinNamedPrefixCutoff_eq_iff_least_of_exists hex).symm

theorem eval_fixedPiThreeHartogsCutoffSelectorFormula {P R one γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula
      (standardTuple ![hartogsNumberName P R (checkName one γ)]))
    (hex : ∃ η, IsWoodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) η) :
    fixedPiThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, one, γ] ↔
      δ = woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) := by
  have hb : fixedPiThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, one, γ] ↔
      ∀ d : V, fixedSigmaThreeHartogsCutoffSelectorFormula.Evalb ![d, P, R, one, γ] → δ = d := by
    simp [fixedPiThreeHartogsCutoffSelectorFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [eval_fixedSigmaThreeHartogsCutoffSelectorFormula hR ht hz hex]
  simp

theorem woodinSparse_fixed_hartogsSelector_iff {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) (δ : V) :
    let c := woodinSparsePrefixCode θ
    let P := woodinSparseInverseBase θ c
    let R := woodinSparseInverseOrder θ c
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
    (fixedSigmaThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, ∅, γ] ↔
      δ = (kpair.π₂ (woodinIterationRec θ)) ‘ θ) ∧
    (fixedPiThreeHartogsCutoffSelectorFormula.Evalb ![δ, P, R, ∅, γ] ↔
      δ = (kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  dsimp only
  obtain ⟨hR, ht, _, hz, hleast⟩ := woodinSparse_fixed_inverseCutoff_context hΩ hAC hθ h0 hlim hn
  have hs := eval_fixedSigmaThreeHartogsCutoffSelectorFormula (δ := δ) hR ht hz ⟨_, hleast.2.1⟩
  have hp := eval_fixedPiThreeHartogsCutoffSelectorFormula (δ := δ) hR ht hz ⟨_, hleast.2.1⟩
  change _ ↔ δ = woodinSparseInverseCutoff θ (woodinSparsePrefixCode θ) at hs hp
  let := hΩ.inaccessible.1
  rw [woodinSparsePrefix_inverse_cutoff hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ) h0 hlim hn] at hs hp
  exact ⟨hs, hp⟩

end ZFVP
