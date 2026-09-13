import ZFVP.Syntax.UniformFormulaSubstitution
import ZFVP.Syntax.UniformNegation
import ZFVP.Syntax.MembershipRenaming

/-! Substitution and negation commute on every internal formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_negate {L Γ Δ G : V} (hL : IsLanguageCode L)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L Γ Δ (G ‘ k))
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k))) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, negateFormula L Γ n φ⟩ₖ, k⟩ₖ =
        negateFormula L Δ (stateTarget (G ‘ k)) ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) := by
  have hv := formulaSubstitutionGraph_valid hL hG hsource htarget
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, negateFormula L Γ n φ⟩ₖ, k⟩ₖ =
      negateFormula L Δ (stateTarget (G ‘ k)) ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)) (by definability)
  · intro n hn
    constructor
    · intro k hk _
      rw [negateFormula_truth hL hn, formulaSubstitutionGraph_falsity hL hn hk,
        formulaSubstitutionGraph_truth hL hn hk, negateFormula_truth hL (hG k hk).2.1]
    · intro k hk _
      rw [negateFormula_falsity hL hn, formulaSubstitutionGraph_truth hL hn hk,
        formulaSubstitutionGraph_falsity hL hn hk, negateFormula_falsity hL (hG k hk).2.1]
  · intro n hn r args ha
    have hat : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        IsAtomicArguments L Δ (stateTarget (G ‘ k)) r
          (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) := by
      intro k hk hctx
      exact atomicArguments_substituted hL hn (hG k hk).2.1
        (hctx.symm ▸ (hG k hk).2.2.1) (hG k hk).2.2.2 ha
    constructor
    · intro k hk hctx
      rw [negateFormula_atom hL hn ha, formulaSubstitutionGraph_negAtom hL hn hk ha,
        formulaSubstitutionGraph_atom hL hn hk ha, negateFormula_atom hL (hG k hk).2.1 (hat k hk hctx)]
    · intro k hk hctx
      rw [negateFormula_negAtom hL hn ha, formulaSubstitutionGraph_atom hL hn hk ha,
        formulaSubstitutionGraph_negAtom hL hn hk ha, negateFormula_negAtom hL (hG k hk).2.1 (hat k hk hctx)]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hnf := negateFormula_mem hL hφ
    have hng := negateFormula_mem hL hψ
    constructor
    · intro k hk hctx
      rw [negateFormula_and hL hn hφ hψ, formulaSubstitutionGraph_or hL hn hk hnf hng,
        formulaSubstitutionGraph_and hL hn hk hφ hψ,
        negateFormula_and hL (hG k hk).2.1 (hv _ _ hφ k hk hctx) (hv _ _ hψ k hk hctx),
        ihφ k hk hctx, ihψ k hk hctx]
    · intro k hk hctx
      rw [negateFormula_or hL hn hφ hψ, formulaSubstitutionGraph_and hL hn hk hnf hng,
        formulaSubstitutionGraph_or hL hn hk hφ hψ,
        negateFormula_or hL (hG k hk).2.1 (hv _ _ hφ k hk hctx) (hv _ _ hψ k hk hctx),
        ihφ k hk hctx, ihψ k hk hctx]
  · intro n hn φ hφ ih
    have hnf := negateFormula_mem hL hφ
    have hctx' : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) → succ n = stateSource (G ‘ (succ k)) := by
      intro k hk he
      rw [hsource k hk, he]
    have hv' : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ ∈
          formulaSet L Δ (succ (stateTarget (G ‘ k))) := by
      intro k hk he
      simpa only [htarget k hk] using hv _ _ hφ (succ k) (ω_succ_closed hk) (hctx' k hk he)
    constructor
    · intro k hk he
      rw [negateFormula_all hL hn hφ, formulaSubstitutionGraph_exists hL hn hk hnf,
        formulaSubstitutionGraph_all hL hn hk hφ,
        negateFormula_all hL (hG k hk).2.1 (hv' k hk he),
        ih (succ k) (ω_succ_closed hk) (hctx' k hk he), htarget k hk]
    · intro k hk he
      rw [negateFormula_exists hL hn hφ, formulaSubstitutionGraph_all hL hn hk hnf,
        formulaSubstitutionGraph_exists hL hn hk hφ,
        negateFormula_exists hL (hG k hk).2.1 (hv' k hk he),
        ih (succ k) (ω_succ_closed hk) (hctx' k hk he), htarget k hk]

theorem substituteFormula_negate {L Γ Δ s φ : V} (hL : IsLanguageCode L)
    (hs : IsSubstitutionState L Γ Δ s) (hφ : φ ∈ formulaSet L Γ (stateSource s)) :
    substituteFormula L Γ Δ s (negateFormula L Γ (stateSource s) φ) =
      negateFormula L Δ (stateTarget s) (substituteFormula L Γ Δ s φ) := by
  have h := formulaSubstitutionGraph_negate (G := substitutionStates L Δ s) hL
    (fun k hk ↦ substitutionStates_valid hL hs hk)
    (fun k hk ↦ by rw [substitutionStates_succ _ _ _ hk]; simp [liftSubstitutionState])
    (fun k hk ↦ by rw [substitutionStates_succ _ _ _ hk]; simp [liftSubstitutionState])
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [substitutionStates_zero])
  simpa only [substitutionStates_zero, substituteFormula] using h

theorem renameMembershipFormula_negate {n m r φ : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula n m r (negateFormula membershipLanguageCode ∅ n φ) =
      negateFormula membershipLanguageCode ∅ m (renameMembershipFormula n m r φ) := by
  have h := substituteFormula_negate membershipLanguageCode_valid (membershipRenaming_state hn hm hr)
    (by simpa only [stateSource_code] using hφ)
  simpa only [renameMembershipFormula, stateSource_code, stateTarget_code] using h

theorem renameMembershipFormula_truth {n : V} (hn : n ∈ (ω : V)) (m r : V) :
    renameMembershipFormula n m r truthCode = (truthCode : V) := by
  unfold renameMembershipFormula substituteFormula
  simp only [stateSource_code]
  exact formulaSubstitutionGraph_truth membershipLanguageCode_valid hn (by simp) ∅ _

theorem renameMembershipFormula_falsity {n : V} (hn : n ∈ (ω : V)) (m r : V) :
    renameMembershipFormula n m r falsityCode = (falsityCode : V) := by
  unfold renameMembershipFormula substituteFormula
  simp only [stateSource_code]
  exact formulaSubstitutionGraph_falsity membershipLanguageCode_valid hn (by simp) ∅ _

end ZFVP
