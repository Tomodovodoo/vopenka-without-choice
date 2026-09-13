import ZFVP.Syntax.AtomicSubstitutionSemantics
import ZFVP.Syntax.LiftSubstitutionSemantics
import ZFVP.Syntax.FormulaSubstitutionValidity
import ZFVP.Syntax.PackedSatisfaction

/-! The semantic substitution law over the entire internal formula family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def substitutionTargetEvaluation (L Δ M e G k b : V) : V :=
  evaluateWithFreeAssignment L Δ M e (stateTarget (G ‘ k)) b

instance substitutionTargetEvaluation_definable (L Δ M e G : V) :
    ℒₛₑₜ-function₂ (substitutionTargetEvaluation L Δ M e G) := by
  unfold substitutionTargetEvaluation
  definability

theorem satisfies_substitutionGraph {L Γ Δ G M e : V} (hM : IsStructureCode L M)
    (he : e ∈ structureDomain M ^ Δ)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L Γ Δ (G ‘ k))
    (hstep : ∀ k ∈ (ω : V), G ‘ (succ k) = liftSubstitutionState L Δ (G ‘ k)) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
        (Satisfies L Δ M e (stateTarget (G ‘ k))
          ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) b ↔
        Satisfies L Γ M (compose (stateFree (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) n φ
          (compose (stateBound (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b))) := by
  have hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)) := by
    intro k hk; simp [hstep k hk, liftSubstitutionState]
  have htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k)) := by
    intro k hk; simp [hstep k hk, liftSubstitutionState]
  have hv := formulaSubstitutionGraph_valid hM.language hG hsource htarget
  have hT : ∀ k ∈ (ω : V), ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
      substitutionTargetEvaluation L Δ M e G k b ∈ structureDomain M ^ termSet L Δ (stateTarget (G ‘ k)) := by
    intro k hk b hb
    exact termEvaluation_mem_function hM (hG k hk).2.1 Δ hb he
  apply formulaSet_induction hM.language Γ (fun n φ ↦
    ∀ k ∈ (ω : V), n = stateSource (G ‘ k) → ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
      (Satisfies L Δ M e (stateTarget (G ‘ k))
        ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) b ↔
      Satisfies L Γ M (compose (stateFree (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) n φ
        (compose (stateBound (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)))) (by
          unfold Satisfies
          definability)
  · intro n hn
    constructor
    · intro k hk hctx b hb
      rw [formulaSubstitutionGraph_truth hM.language hn hk,
        satisfies_truth hM.language (hG k hk).2.1, satisfies_truth hM.language hn]
      exact iff_of_true hb (hctx.symm ▸ compose_function (hG k hk).2.2.1 (hT k hk b hb))
    · intro k hk _ b _
      rw [formulaSubstitutionGraph_falsity hM.language hn hk]
      exact iff_of_false (not_satisfies_falsity hM.language (hG k hk).2.1)
        (not_satisfies_falsity hM.language hn)
  · intro n hn r args ha
    have hcommon : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
        AtomicHolds L Δ M e (stateTarget (G ‘ k)) b r
          (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) ↔
        AtomicHolds L Γ M (compose (stateFree (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) n
          (compose (stateBound (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) r args := by
      intro k hk hctx b hb
      exact atomicHolds_substitution hM hn (hG k hk).2.1
        (hctx.symm ▸ (hG k hk).2.2.1) (hG k hk).2.2.2 hb he ha
    constructor
    · intro k hk hctx b hb
      have hB := hctx.symm ▸ (hG k hk).2.2.1
      rw [formulaSubstitutionGraph_atom hM.language hn hk ha,
        satisfies_atom hM.language (hG k hk).2.1
          (atomicArguments_substituted hM.language hn (hG k hk).2.1 hB (hG k hk).2.2.2 ha) hb,
        satisfies_atom hM.language hn ha (compose_function hB (hT k hk b hb))]
      exact hcommon k hk hctx b hb
    · intro k hk hctx b hb
      have hB := hctx.symm ▸ (hG k hk).2.2.1
      rw [formulaSubstitutionGraph_negAtom hM.language hn hk ha,
        satisfies_negAtom hM.language (hG k hk).2.1
          (atomicArguments_substituted hM.language hn (hG k hk).2.1 hB (hG k hk).2.2.2 ha) hb,
        satisfies_negAtom hM.language hn ha (compose_function hB (hT k hk b hb))]
      exact not_congr (hcommon k hk hctx b hb)
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk hctx b hb
      rw [formulaSubstitutionGraph_and hM.language hn hk hφ hψ,
        satisfies_and hM.language (hG k hk).2.1 (hv n φ hφ k hk hctx) (hv n ψ hψ k hk hctx) hb,
        satisfies_and hM.language hn hφ hψ
          (hctx.symm ▸ compose_function (hG k hk).2.2.1 (hT k hk b hb))]
      exact and_congr (ihφ k hk hctx b hb) (ihψ k hk hctx b hb)
    · intro k hk hctx b hb
      rw [formulaSubstitutionGraph_or hM.language hn hk hφ hψ,
        satisfies_or hM.language (hG k hk).2.1 (hv n φ hφ k hk hctx) (hv n ψ hψ k hk hctx) hb,
        satisfies_or hM.language hn hφ hψ
          (hctx.symm ▸ compose_function (hG k hk).2.2.1 (hT k hk b hb))]
      exact or_congr (ihφ k hk hctx b hb) (ihψ k hk hctx b hb)
  · intro n hn φ hφ ih
    have hbody : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k), ∀ x ∈ structureDomain M,
        Satisfies L Δ M e (succ (stateTarget (G ‘ k)))
          ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ)
          (assignmentPrepend (stateTarget (G ‘ k)) b x) ↔
        Satisfies L Γ M (compose (stateFree (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) (succ n) φ
          (assignmentPrepend n (compose (stateBound (G ‘ k)) (substitutionTargetEvaluation L Δ M e G k b)) x) := by
      intro k hk hctx b hb x hx
      have hc : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hctx]
      have hb' : assignmentPrepend (stateTarget (G ‘ k)) b x ∈ structureDomain M ^ stateTarget (G ‘ (succ k)) := by
        rw [htarget k hk]; exact assignmentPrepend_mem_function (hG k hk).2.1 hb hx
      have hi := ih (succ k) (ω_succ_closed hk) hc _ hb'
      have hB := evaluate_liftBoundReplacement hM (hG k hk).1 (hG k hk).2.1 (hG k hk).2.2.1 hb he hx
      have hE := evaluate_liftFreeReplacement hM (hG k hk).2.1 (hG k hk).2.2.2 hb he hx
      simp only [hstep k hk, liftSubstitutionState, stateTarget_code, stateBound_code, stateFree_code,
        substitutionTargetEvaluation, evaluateWithFreeAssignment] at hi
      rw [hB, hE] at hi
      simpa only [hctx, substitutionTargetEvaluation, evaluateWithFreeAssignment] using hi
    have hbodymem : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ ∈ formulaSet L Δ (succ (stateTarget (G ‘ k))) := by
      intro k hk hctx
      have hc : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hctx]
      simpa only [htarget k hk] using hv (succ n) φ hφ (succ k) (ω_succ_closed hk) hc
    constructor
    · intro k hk hctx b hb
      rw [formulaSubstitutionGraph_all hM.language hn hk hφ,
        satisfies_all hM.language (hG k hk).2.1 (hbodymem k hk hctx) hb,
        satisfies_all hM.language hn hφ
          (hctx.symm ▸ compose_function (hG k hk).2.2.1 (hT k hk b hb))]
      exact forall_congr' (fun x ↦ forall_congr' (fun hx ↦ hbody k hk hctx b hb x hx))
    · intro k hk hctx b hb
      rw [formulaSubstitutionGraph_exists hM.language hn hk hφ,
        satisfies_exists hM.language (hG k hk).2.1 (hbodymem k hk hctx) hb,
        satisfies_exists hM.language hn hφ
          (hctx.symm ▸ compose_function (hG k hk).2.2.1 (hT k hk b hb))]
      exact exists_congr (fun x ↦ and_congr_right (fun hx ↦ hbody k hk hctx b hb x hx))

theorem satisfies_substituteFormula {L Γ Δ s M e φ b : V} (hM : IsStructureCode L M)
    (hs : IsSubstitutionState L Γ Δ s) (he : e ∈ structureDomain M ^ Δ)
    (hφ : φ ∈ formulaSet L Γ (stateSource s)) (hb : b ∈ structureDomain M ^ stateTarget s) :
    Satisfies L Δ M e (stateTarget s) (substituteFormula L Γ Δ s φ) b ↔
      Satisfies L Γ M (compose (stateFree s) (termEvaluation L Δ (stateTarget s) M b e))
        (stateSource s) φ (compose (stateBound s) (termEvaluation L Δ (stateTarget s) M b e)) := by
  have h := satisfies_substitutionGraph (G := substitutionStates L Δ s) hM he
    (fun k hk ↦ substitutionStates_valid hM.language hs hk)
    (fun k hk ↦ substitutionStates_succ L Δ s hk)
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [substitutionStates_zero]) b
    (by simpa only [substitutionStates_zero] using hb)
  simpa only [substituteFormula, substitutionTargetEvaluation, evaluateWithFreeAssignment,
    substitutionStates_zero] using h

end ZFVP
