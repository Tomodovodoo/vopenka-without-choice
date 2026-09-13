import ZFVP.Syntax.BoundedCodeSubstitution
import ZFVP.Syntax.LevyCodes

/-! Every standard internal Levy class is closed under membership substitution. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_levy {G : V}
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState membershipLanguageCode ∅ ∅ (G ‘ k))
    (hstep : ∀ k ∈ (ω : V), G ‘ (succ k) = liftSubstitutionState membershipLanguageCode ∅ (G ‘ k))
    (l : ℕ) (p : LevyPolarity) :
    ∀ n φ, IsLevyFormulaCode p l n φ → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      IsLevyFormulaCode p l (stateTarget (G ‘ k))
        ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) := by
  induction l generalizing p with
  | zero => exact formulaSubstitutionGraph_bounded hG hstep
  | succ l ih =>
    refine levyFormulaCode_successor_induction l p (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      IsLevyFormulaCode p (l + 1) (stateTarget (G ‘ k))
        ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)) (by definability) ?_ ?_ ?_ ?_
    · intro q n φ hφ k hk hc
      exact (ih q n φ hφ k hk hc).raise
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro k hk hc
        rw [formulaSubstitutionGraph_and membershipLanguageCode_valid hn hk hφ.valid hψ.valid]
        exact (ihφ k hk hc).and (ihψ k hk hc)
      · intro k hk hc
        rw [formulaSubstitutionGraph_or membershipLanguageCode_valid hn hk hφ.valid hψ.valid]
        exact (ihφ k hk hc).or (ihψ k hk hc)
    · intro n hn i hi φ hφ ihφ
      have hbody (k : V) (hk : k ∈ (ω : V)) (hc : n = stateSource (G ‘ k)) :
          IsLevyFormulaCode p (l + 1) (succ (stateTarget (G ‘ k)))
            ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
        have hs : succ n = stateSource (G ‘ (succ k)) := by rw [hstep k hk]; simp [liftSubstitutionState, hc]
        have hh := ihφ (succ k) (ω_succ_closed hk) hs
        simpa only [hstep k hk, liftSubstitutionState, stateTarget_code] using hh
      constructor
      · intro k hk hc
        obtain ⟨j, hj, hij⟩ := substitutionState_bound_index (hG k hk) (hc ▸ hi)
        rw [formulaSubstitutionGraph_boundedAll hn hi hk hφ.valid (hG k hk) hc (hstep k hk) hj hij]
        exact IsLevyFormulaCode.boundedAll (hG k hk).2.1 hj (hbody k hk hc)
      · intro k hk hc
        obtain ⟨j, hj, hij⟩ := substitutionState_bound_index (hG k hk) (hc ▸ hi)
        rw [formulaSubstitutionGraph_boundedExists hn hi hk hφ.valid (hG k hk) hc (hstep k hk) hj hij]
        exact IsLevyFormulaCode.boundedExists (hG k hk).2.1 hj (hbody k hk hc)
    · intro n hn φ hφ ihφ k hk hc
      have hs : succ n = stateSource (G ‘ (succ k)) := by rw [hstep k hk]; simp [liftSubstitutionState, hc]
      have hh := ihφ (succ k) (ω_succ_closed hk) hs
      have hbody : IsLevyFormulaCode p (l + 1) (succ (stateTarget (G ‘ k)))
          ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
        simpa only [hstep k hk, liftSubstitutionState, stateTarget_code] using hh
      cases p with
      | sigma =>
        simp only [levyQuantifierCode]
        rw [formulaSubstitutionGraph_exists membershipLanguageCode_valid hn hk hφ.valid]
        exact IsLevyFormulaCode.quantifier (hG k hk).2.1 hbody
      | pi =>
        simp only [levyQuantifierCode]
        rw [formulaSubstitutionGraph_all membershipLanguageCode_valid hn hk hφ.valid]
        exact IsLevyFormulaCode.quantifier (hG k hk).2.1 hbody

theorem substituteFormula_levy {p : LevyPolarity} {l : ℕ} {s φ : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hφ : IsLevyFormulaCode p l (stateSource s) φ) :
    IsLevyFormulaCode p l (stateTarget s) (substituteFormula membershipLanguageCode ∅ ∅ s φ) := by
  have h := formulaSubstitutionGraph_levy (G := substitutionStates membershipLanguageCode ∅ s)
    (fun k hk ↦ substitutionStates_valid membershipLanguageCode_valid hs hk)
    (fun k hk ↦ substitutionStates_succ membershipLanguageCode ∅ s hk) l p
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [substitutionStates_zero])
  simpa only [substitutionStates_zero, substituteFormula] using h

end ZFVP
