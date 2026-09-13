import ZFVP.Syntax.MembershipSubstitutionGuards
import ZFVP.Syntax.SubstitutionStateDefinability

/-! Internal bounded syntax is closed under capture-avoiding membership substitution. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_bounded {G : V}
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState membershipLanguageCode ∅ ∅ (G ‘ k))
    (hstep : ∀ k ∈ (ω : V), G ‘ (succ k) = liftSubstitutionState membershipLanguageCode ∅ (G ‘ k)) :
    ∀ n φ, IsBoundedFormulaCode n φ → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      IsBoundedFormulaCode (stateTarget (G ‘ k))
        ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) := by
  suffices h : ∀ q ∈ (boundedFormulaFamily : V), ∀ k ∈ (ω : V), kpair.π₁ q = stateSource (G ‘ k) →
      IsBoundedFormulaCode (stateTarget (G ‘ k))
        ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨q, k⟩ₖ) by
    intro n φ hφ
    simpa using h ⟨n, φ⟩ₖ hφ
  refine boundedFormulaFamily_induction (fun q : V ↦ ∀ k ∈ (ω : V), kpair.π₁ q = stateSource (G ‘ k) →
    IsBoundedFormulaCode (stateTarget (G ‘ k))
      ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨q, k⟩ₖ)) (by definability) ?_ ?_ ?_ ?_
  all_goals simp only [kpair.π₁_kpair]
  · intro n hn
    constructor
    · intro k hk _
      rw [formulaSubstitutionGraph_truth membershipLanguageCode_valid hn hk]
      exact (boundedFormulaFamily_closed _ (hG k hk).2.1).1.1
    · intro k hk _
      rw [formulaSubstitutionGraph_falsity membershipLanguageCode_valid hn hk]
      exact (boundedFormulaFamily_closed _ (hG k hk).2.1).1.2
  · intro n hn r args ha
    have hv (k : V) (hk : k ∈ (ω : V)) (hc : n = stateSource (G ‘ k)) :
        IsAtomicArguments membershipLanguageCode ∅ (stateTarget (G ‘ k)) r
          (compose args (termSubstitution membershipLanguageCode ∅ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) :=
      atomicArguments_substituted membershipLanguageCode_valid hn (hG k hk).2.1
        (hc.symm ▸ (hG k hk).2.2.1) (hG k hk).2.2.2 ha
    constructor
    · intro k hk hc
      rw [formulaSubstitutionGraph_atom membershipLanguageCode_valid hn hk ha]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.1 _ _ (hv k hk hc)).1
    · intro k hk hc
      rw [formulaSubstitutionGraph_negAtom membershipLanguageCode_valid hn hk ha]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.1 _ _ (hv k hk hc)).2
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk hc
      rw [formulaSubstitutionGraph_and membershipLanguageCode_valid hn hk (IsBoundedFormulaCode.valid hφ) (IsBoundedFormulaCode.valid hψ)]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.2.1 _ _ (ihφ k hk hc) (ihψ k hk hc)).1
    · intro k hk hc
      rw [formulaSubstitutionGraph_or membershipLanguageCode_valid hn hk (IsBoundedFormulaCode.valid hφ) (IsBoundedFormulaCode.valid hψ)]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.2.1 _ _ (ihφ k hk hc) (ihψ k hk hc)).2
  · intro n hn i hi φ hφ ih
    have hbody (k : V) (hk : k ∈ (ω : V)) (hc : n = stateSource (G ‘ k)) :
        IsBoundedFormulaCode (succ (stateTarget (G ‘ k)))
          ((formulaSubstitutionGraph membershipLanguageCode ∅ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
      have hs : succ n = stateSource (G ‘ (succ k)) := by rw [hstep k hk]; simp [liftSubstitutionState, hc]
      have hh := ih (succ k) (ω_succ_closed hk) hs
      simpa only [hstep k hk, liftSubstitutionState, stateTarget_code] using hh
    constructor
    · intro k hk hc
      obtain ⟨j, hj, hij⟩ := substitutionState_bound_index (hG k hk) (hc ▸ hi)
      rw [formulaSubstitutionGraph_boundedAll hn hi hk (IsBoundedFormulaCode.valid hφ) (hG k hk) hc (hstep k hk) hj hij]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.2.2 j hj _ (hbody k hk hc)).1
    · intro k hk hc
      obtain ⟨j, hj, hij⟩ := substitutionState_bound_index (hG k hk) (hc ▸ hi)
      rw [formulaSubstitutionGraph_boundedExists hn hi hk (IsBoundedFormulaCode.valid hφ) (hG k hk) hc (hstep k hk) hj hij]
      exact ((boundedFormulaFamily_closed _ (hG k hk).2.1).2.2.2 j hj _ (hbody k hk hc)).2

theorem substituteFormula_bounded {s φ : V} (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hφ : IsBoundedFormulaCode (stateSource s) φ) :
    IsBoundedFormulaCode (stateTarget s) (substituteFormula membershipLanguageCode ∅ ∅ s φ) := by
  have h := formulaSubstitutionGraph_bounded (G := substitutionStates membershipLanguageCode ∅ s)
    (fun k hk ↦ substitutionStates_valid membershipLanguageCode_valid hs hk)
    (fun k hk ↦ substitutionStates_succ membershipLanguageCode ∅ s hk)
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [substitutionStates_zero])
  simpa only [substitutionStates_zero, substituteFormula] using h

end ZFVP
