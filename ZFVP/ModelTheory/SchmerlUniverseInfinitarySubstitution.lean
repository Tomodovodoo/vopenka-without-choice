import ZFVP.ModelTheory.SchmerlUniverseInfinitaryCodes
import ZFVP.ModelTheory.SchmerlInternalInfinitarySubstitutionSemantics
import ZFVP.ModelTheory.InfinitaryTermSubstitution
import ZFVP.Syntax.FoundationFormulaSubstitution

/-! The actual internal infinitary substitution graph agrees with external
capture-avoiding substitution on every encoded formula. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

variable {Λ : Language}

theorem subst_q_bvar {n m : ℕ} (σ : Fin n → Semiterm Λ Empty m) (i : Fin (n + 1)) :
    (Rew.subst σ).q (.bvar i) = liftSubstitution σ i := by
  cases i using Fin.cases <;> simp [liftSubstitution]

set_option maxHeartbeats 1000000 in
theorem universeFormulaCode_subst_graph {L H G : Universe.{u}} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : Universe.{u}))
    (hH : IsFragment L H)
    (hG : ∀ k ∈ (ω : Universe.{u}), IsSubstitutionState L ∅ ∅ (G ‘ k))
    (hstep : ∀ k ∈ (ω : Universe.{u}), G ‘ (succ k) = liftSubstitutionState L ∅ (G ‘ k))
    {n : ℕ} (φ : Formula Λ n) {m : ℕ} {k : Universe.{u}}
    (σ : Fin n → Semiterm Λ Empty m) (hk : k ∈ (ω : Universe.{u}))
    (hn : stateSource (G ‘ k) = (n : Universe.{u})) (hm : stateTarget (G ‘ k) = (m : Universe.{u}))
    (hB : ∀ i : Fin n, (stateBound (G ‘ k)) ‘ (i.val : Universe.{u}) = encodeSemiterm F Empty.elim (σ i))
    (hφ : ⟨(n : Universe.{u}), universeFormulaCode F R φ⟩ₖ ∈ H) :
    (infinitarySubstitutionGraph L H G) ‘ ⟨⟨(n : Universe.{u}), universeFormulaCode F R φ⟩ₖ, k⟩ₖ =
      universeFormulaCode F R (φ.subst σ) := by
  induction φ generalizing m k with
  | fo φ =>
    rw [universeFormulaCode, infinitarySubstitutionGraph_fo hφ hk]
    exact congrArg foCode (encodeSemiformula_rew_graph hL F R Empty.elim Empty.elim hF hR
      (fun x ↦ Empty.elim x) (fun x ↦ Empty.elim x) hstep hk (hG k hk) hn hm (Rew.subst σ)
      (by simpa using hB) (fun x ↦ Empty.elim x) φ)
  | neg φ ih =>
    have hchild := hH.immediate_mem hφ ((immediate_neg_iff _ _ _).mpr rfl)
    rw [universeFormulaCode, infinitarySubstitutionGraph_neg hH hφ hk, ih σ hk hn hm hB hchild]
    rfl
  | conj φ ih =>
    rw [universeFormulaCode, infinitarySubstitutionGraph_conj hH hφ hk]
    change conjCode _ = conjCode _
    congr 1
    apply functions_eq_of_domain_values (by simp)
    intro i hi
    rw [domain_transformConjunction] at hi
    obtain ⟨j, rfl⟩ := universe_standardOmega i hi
    rw [value_transformConjunction _ _ _ (by simp), value_universeSequence]
    simp only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair, value_universeSequence]
    apply ih j σ hk hn hm hB
    have hc := hH.immediate_mem hφ ((immediate_conj_iff _ _ _).mpr
      ⟨inferInstance, (j : Universe.{u}), by simp, rfl⟩)
    simpa only [value_universeSequence] using hc
  | @exs n φ ih =>
    have hc : ⟨((n + 1 : ℕ) : Universe.{u}), universeFormulaCode F R φ⟩ₖ ∈ H := by
      simpa only [num_succ_def] using hH.immediate_mem hφ ((immediate_exs_iff _ _ _).mpr rfl)
    have hn' : stateSource (G ‘ (succ k)) = ((n + 1 : ℕ) : Universe.{u}) := by
      simp [hstep k hk, liftSubstitutionState, hn, num_succ_def]
    have hm' : stateTarget (G ‘ (succ k)) = ((m + 1 : ℕ) : Universe.{u}) := by
      simp [hstep k hk, liftSubstitutionState, hm, num_succ_def]
    have hb := liftBoundReplacement_encode hL F Empty.elim hF (fun x ↦ Empty.elim x)
      (Rew.subst σ) (by simpa [hn, hm] using (hG k hk).2.2.1) (by simpa using hB)
    have hb' : ∀ i : Fin (n + 1), (stateBound (G ‘ (succ k))) ‘ (i.val : Universe.{u}) =
        encodeSemiterm F Empty.elim (liftSubstitution σ i) := by
      simpa only [hstep k hk, liftSubstitutionState, stateBound_code, hn, hm, subst_q_bvar] using hb
    rw [universeFormulaCode, infinitarySubstitutionGraph_exs hH hφ hk]
    have h := ih (liftSubstitution σ) (ω_succ_closed hk) hn' hm' hb' hc
    simpa only [num_succ_def, Formula.subst, universeFormulaCode] using congrArg exsCode h
  | @q n φ ih =>
    have hc : ⟨((n + 1 : ℕ) : Universe.{u}), universeFormulaCode F R φ⟩ₖ ∈ H := by
      simpa only [num_succ_def] using hH.immediate_mem hφ ((immediate_q_iff _ _ _).mpr rfl)
    have hn' : stateSource (G ‘ (succ k)) = ((n + 1 : ℕ) : Universe.{u}) := by
      simp [hstep k hk, liftSubstitutionState, hn, num_succ_def]
    have hm' : stateTarget (G ‘ (succ k)) = ((m + 1 : ℕ) : Universe.{u}) := by
      simp [hstep k hk, liftSubstitutionState, hm, num_succ_def]
    have hb := liftBoundReplacement_encode hL F Empty.elim hF (fun x ↦ Empty.elim x)
      (Rew.subst σ) (by simpa [hn, hm] using (hG k hk).2.2.1) (by simpa using hB)
    have hb' : ∀ i : Fin (n + 1), (stateBound (G ‘ (succ k))) ‘ (i.val : Universe.{u}) =
        encodeSemiterm F Empty.elim (liftSubstitution σ i) := by
      simpa only [hstep k hk, liftSubstitutionState, stateBound_code, hn, hm, subst_q_bvar] using hb
    rw [universeFormulaCode, infinitarySubstitutionGraph_q hH hφ hk]
    have h := ih (liftSubstitution σ) (ω_succ_closed hk) hn' hm' hb' hc
    simpa only [num_succ_def, Formula.subst, universeFormulaCode] using congrArg qCode h

end ZFVP.Infinitary.Internal
