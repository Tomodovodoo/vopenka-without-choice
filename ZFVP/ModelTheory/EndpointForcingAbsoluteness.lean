import ZFVP.ModelTheory.UniformForcingDefinitions
import ZFVP.SetTheory.CnAbsoluteness

/-! The internal forcing relation is Delta one, hence unchanged by passing to a correct rank.

The paper's endpoint lemma argues in an outer model where a rank initial segment has become
countable, and needs the forcing relation to be the same there.  The replacement used here is a
complexity certificate: `sigmaOneInternalForcingFormula` and its universal companion
`piOneInternalForcingFormula` both define `InternalForces`, one Sigma one and the other Pi one.
A Delta one relation is computed the same way inside any `Cn 1` rank stage as in `V`, which is
what `internalForces_absolute` says.  The same holds at the exact Levy bound of the level
formulas of the uniform dictionary.

Nothing here mentions a forcing iteration or an endpoint: every statement is parametric in the
poset `P`, the order `R` and the name set `D`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### The Pi one companion of the Sigma one forcing formula -/

/-- The universal reading of the internal forcing relation: every sequence support containing the
poset and the name set, every omega code, every membership formula family, every atomic truth
table and every internal forcing table over them make the lookup succeed. -/
def piOneInternalForcingFormula : SetTheorySemisentence 7 :=
  “P R D n φ b p. ∀ U, !sequenceSupportFormula U → P ∈ U → D ∈ U →
    ∀ O, !boundedOmegaFormula O → ∀ F, !sigmaOneMembershipFamilyFormula F →
    ∀ H, !boundedAtomicTruthTableFormula U P R H →
    ∀ T, !boundedInternalForcingTableFormula U O F P R D H T →
      !(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b p n φ”

theorem piOneInternalForcingFormula_piOne : IsPiFormula 1 piOneInternalForcingFormula := by
  unfold piOneInternalForcingFormula
  refine .all (.or (.bounded (sequenceSupportFormula_bounded.subst _).neg)
    (.or (.bounded (IsBoundedSetFormula.neg (.rel _ _)))
      (.or (.bounded (IsBoundedSetFormula.neg (.rel _ _)))
        (.all (.or (.bounded (boundedOmegaFormula_bounded.subst _).neg)
          (.all (.or (sigmaOneMembershipFamilyFormula_sigmaOne.subst _).neg
            (.all (.or (.bounded (boundedAtomicTruthTableFormula_bounded.subst _).neg)
              (.all (.or (.bounded (boundedInternalForcingTableFormula_bounded.subst _).neg)
                (.bounded ((CodeExpression.kpair (.var 0)
                  (.var 1)).forcingLookupFormula_bounded.subst _)))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piOneInternalForcingFormula {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    piOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔ InternalForces P R D n φ b p := by
  have hm : piOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔
      ∀ U : V, IsSequenceSupport U → P ∈ U → D ∈ U →
        ∀ H : V, boundedAtomicTruthTableFormula.Evalb ![U, P, R, H] →
          ∀ T : V, boundedInternalForcingTableFormula.Evalb
              ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] →
            (CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula.Evalb
              ![U, T, b, p, n, φ] := by
    simp [piOneInternalForcingFormula, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]
  rw [hm]
  have hlocal (U : V) (hU : IsSequenceSupport U) (hP : P ∈ U) (hD : D ∈ U) :
      (∀ H : V, boundedAtomicTruthTableFormula.Evalb ![U, P, R, H] →
        ∀ T : V, boundedInternalForcingTableFormula.Evalb
            ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] →
          (CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula.Evalb ![U, T, b, p, n, φ]) ↔
      InternalForces P R D n φ b p := by
    let := hU
    have hPs : P ⊆ U := hU.toIsTransitive.transitive P hP
    have hDs : D ⊆ U := hU.toIsTransitive.transitive D hD
    have hbu := function_mem_sequenceSupport hDs hφ.context hb
    have hnu : n ∈ U := IsCodingSupport.natural_mem hφ.context
    have hφu : φ ∈ U := membershipFormulaCode_formula_mem_support hφ
    constructor
    · intro h
      obtain ⟨H, hH⟩ := atomicTruthTable_exists P R U (transitive_subnameClosed hU.toIsTransitive)
      have ht := h H ((eval_boundedAtomicTruthTableFormula P R H).mpr hH)
        (internalForcingTruthTable P R D)
        ((eval_boundedInternalForcingTableFormula hPs hDs hH _).mpr
          (internalForcingTruthTable_correct P R D))
      have hl := (CodeExpression.eval_forcingLookupFormula_two (.kpair (.var 0) (.var 1)) _ hbu
        (hPs p hp) hnu hφu).mp ht
      exact (internalForcingTruthTable_lookup hφ hb hp).mp hl
    · intro ht H hH T hT
      have hH := (eval_boundedAtomicTruthTableFormula P R H).mp hH
      have hT : IsInternalForcingTruthTable P R D T :=
        (eval_boundedInternalForcingTableFormula hPs hDs hH T).mp hT
      apply (CodeExpression.eval_forcingLookupFormula_two (.kpair (.var 0) (.var 1)) _ hbu
        (hPs p hp) hnu hφu).mpr
      exact (hT.lookup hφ hb hp).mpr ht
  constructor
  · intro h
    obtain ⟨U, hU, hpair⟩ := sequenceSupport_containing (⟨P, D⟩ₖ : V)
    let := hU
    obtain ⟨hP, hD⟩ := kpair_components_mem_transitive hpair
    exact (hlocal U hU hP hD).mp (h U hU hP hD)
  · intro ht U hU hP hD
    exact (hlocal U hU hP hD).mpr ht

/-- The forcing relation has both a Sigma one and a Pi one definition, in the same seven free
variables and with the same arguments. -/
theorem internalForces_deltaOne {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    (sigmaOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔
      InternalForces P R D n φ b p) ∧
    (piOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔
      InternalForces P R D n φ b p) :=
  ⟨eval_sigmaOneInternalForcingFormula hφ hb hp, eval_piOneInternalForcingFormula hφ hb hp⟩

/-! ### Absoluteness between a correct rank stage and `V` -/

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem vec_val_seven {a : V} (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : SetDomain a) :
    (fun i : Fin 7 ↦ (![x₀, x₁, x₂, x₃, x₄, x₅, x₆] i).val) =
      ![x₀.val, x₁.val, x₂.val, x₃.val, x₄.val, x₅.val, x₆.val] := by
  funext i
  exact Fin.cases rfl (fun i₁ ↦ Fin.cases rfl (fun i₂ ↦ Fin.cases rfl (fun i₃ ↦ Fin.cases rfl
    (fun i₄ ↦ Fin.cases rfl (fun i₅ ↦ Fin.cases rfl (fun i₆ ↦ Fin.cases rfl
      (fun i₇ ↦ Fin.elim0 i₇) i₆) i₅) i₄) i₃) i₂) i₁) i

private theorem evalb_seven_absolute {p : LevyPolarity} {m : ℕ} {ξ : V} (hξ : Cn (m + 1) ξ)
    {ψ : SetTheorySemisentence 7} (hψ : IsLevyFormula p (m + 1) ψ)
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : SetDomain (hierarchy ξ)) :
    ψ.Evalb ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] ↔
      ψ.Evalb ![x₀.val, x₁.val, x₂.val, x₃.val, x₄.val, x₅.val, x₆.val] := by
  have hc := hξ.levy_correct hψ ![x₀, x₁, x₂, x₃, x₄, x₅, x₆]
  rwa [vec_val_seven] at hc

/-- The Sigma one forcing formula, evaluated inside a `Cn 1` rank stage that contains all seven
arguments, defines the true forcing relation of `V`.  Collapsing that stage in an outer model
therefore cannot change which conditions force what. -/
theorem internalForces_absolute {ξ P R D n φ b p : V} (hξ : Cn 1 ξ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ' : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hp' : p ∈ hierarchy ξ) :
    sigmaOneInternalForcingFormula.Evalb
      (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ'⟩, ⟨b, hb'⟩, ⟨p, hp'⟩] :
        Fin 7 → SetDomain (hierarchy ξ)) ↔
      InternalForces P R D n φ b p := by
  exact (evalb_seven_absolute hξ sigmaOneInternalForcingFormula_sigmaOne
    ⟨P, hP⟩ ⟨R, hR⟩ ⟨D, hD⟩ ⟨n, hn⟩ ⟨φ, hφ'⟩ ⟨b, hb'⟩ ⟨p, hp'⟩).trans
    (eval_sigmaOneInternalForcingFormula hφ hb hp)

/-- The Pi one companion is absolute for the same stages, so the two definitions agree there. -/
theorem piOneInternalForces_absolute {ξ P R D n φ b p : V} (hξ : Cn 1 ξ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ' : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hp' : p ∈ hierarchy ξ) :
    piOneInternalForcingFormula.Evalb
      (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ'⟩, ⟨b, hb'⟩, ⟨p, hp'⟩] :
        Fin 7 → SetDomain (hierarchy ξ)) ↔
      InternalForces P R D n φ b p := by
  exact (evalb_seven_absolute hξ piOneInternalForcingFormula_piOne
    ⟨P, hP⟩ ⟨R, hR⟩ ⟨D, hD⟩ ⟨n, hn⟩ ⟨φ, hφ'⟩ ⟨b, hb'⟩ ⟨p, hp'⟩).trans
    (eval_piOneInternalForcingFormula hφ hb hp)

/-! ### The level formulas of the uniform dictionary -/

/-- The Pi companion of `uniformForcingLevelFormula`, at the same Levy bound. -/
def uniformForcingLevelPiFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 7 :=
  “P R D n φ b q. !(isLevyFormulaCodeFormula p k) n φ ∧
    !piOneInternalForcingFormula P R D n φ b q”

theorem uniformForcingLevelPiFormula_pi (p : LevyPolarity) (k : ℕ) :
    IsPiFormula (uniformForcingLevelBound p k) (uniformForcingLevelPiFormula p k) :=
  .and (((levyFormulaCodeFormula_complexity p k .pi).subst _).mono (Nat.le_max_right _ _))
    ((piOneInternalForcingFormula_piOne.subst _).mono (Nat.le_max_left _ _))

theorem eval_uniformForcingLevelPiFormula {pol : LevyPolarity} {k : ℕ} {P R D n φ b q : V}
    (hb : b ∈ D ^ n) (hq : q ∈ P) :
    (uniformForcingLevelPiFormula pol k).Evalb ![P, R, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b := by
  have h : (uniformForcingLevelPiFormula pol k).Evalb ![P, R, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧
        piOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, q] := by
    simp [uniformForcingLevelPiFormula, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]
  rw [h]
  refine and_congr_right fun hc ↦ ?_
  exact (eval_piOneInternalForcingFormula hc.membershipCode hb hq).trans
    (mem_internalForcingSet hc.membershipCode).symm

private theorem uniformForcingLevelBound_succ (p : LevyPolarity) (k : ℕ) :
    ∃ m, uniformForcingLevelBound p k = m + 1 :=
  ⟨uniformForcingLevelBound p k - 1, by
    have : 1 ≤ uniformForcingLevelBound p k := Nat.le_max_left _ _
    omega⟩

/-- The Sigma level formula of the uniform dictionary, evaluated inside a rank stage correct up to
its own Levy bound, defines the true forcing relation of `V` on codes of that level. -/
theorem uniformForcingLevel_absolute {pol : LevyPolarity} {k : ℕ} {ξ P R D n φ b q : V}
    (hξ : Cn (uniformForcingLevelBound pol k) ξ) (hb : b ∈ D ^ n) (hq : q ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hq' : q ∈ hierarchy ξ) :
    (uniformForcingLevelFormula pol k).Evalb
      (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
        Fin 7 → SetDomain (hierarchy ξ)) ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b := by
  obtain ⟨m, hm⟩ := uniformForcingLevelBound_succ pol k
  have hξ' : Cn (m + 1) ξ := hm ▸ hξ
  have hs : IsLevyFormula .sigma (m + 1) (uniformForcingLevelFormula pol k) :=
    hm ▸ uniformForcingLevelFormula_sigma pol k
  exact (evalb_seven_absolute hξ' hs ⟨P, hP⟩ ⟨R, hR⟩ ⟨D, hD⟩ ⟨n, hn⟩ ⟨φ, hφ⟩ ⟨b, hb'⟩
    ⟨q, hq'⟩).trans (eval_uniformForcingLevelFormula hb hq)

/-- The Pi companion of the level formula is absolute for the same stages. -/
theorem uniformForcingLevelPi_absolute {pol : LevyPolarity} {k : ℕ} {ξ P R D n φ b q : V}
    (hξ : Cn (uniformForcingLevelBound pol k) ξ) (hb : b ∈ D ^ n) (hq : q ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hq' : q ∈ hierarchy ξ) :
    (uniformForcingLevelPiFormula pol k).Evalb
      (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
        Fin 7 → SetDomain (hierarchy ξ)) ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b := by
  obtain ⟨m, hm⟩ := uniformForcingLevelBound_succ pol k
  have hξ' : Cn (m + 1) ξ := hm ▸ hξ
  have hs : IsLevyFormula .pi (m + 1) (uniformForcingLevelPiFormula pol k) :=
    hm ▸ uniformForcingLevelPiFormula_pi pol k
  exact (evalb_seven_absolute hξ' hs ⟨P, hP⟩ ⟨R, hR⟩ ⟨D, hD⟩ ⟨n, hn⟩ ⟨φ, hφ⟩ ⟨b, hb'⟩
    ⟨q, hq'⟩).trans (eval_uniformForcingLevelPiFormula hb hq)

end ZFVP
