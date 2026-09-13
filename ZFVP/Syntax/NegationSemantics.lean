import ZFVP.Syntax.FormulaNegation
import ZFVP.Syntax.SatisfactionEquations
import ZFVP.Syntax.FoundationEncoding

/-! Negation complements satisfaction for every valid internal formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfies_negateFormula {L Γ M e n φ b : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ n) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (negateFormula L Γ n φ) b ↔ ¬Satisfies L Γ M e n φ b := by
  classical
  have hall : ∀ n φ, φ ∈ formulaSet L Γ n → ∀ b ∈ structureDomain M ^ n,
      Satisfies L Γ M e n (negateFormula L Γ n φ) b ↔ ¬Satisfies L Γ M e n φ b := by
    apply formulaSet_induction hL Γ (fun n φ ↦ ∀ b ∈ structureDomain M ^ n,
      Satisfies L Γ M e n (negateFormula L Γ n φ) b ↔ ¬Satisfies L Γ M e n φ b) (by
        unfold Satisfies
        definability)
    · intro n hn
      constructor
      · intro b hb
        rw [negateFormula_truth hL hn]
        exact iff_of_false (not_satisfies_falsity hL hn) (not_not_intro ((satisfies_truth hL hn).mpr hb))
      · intro b hb
        rw [negateFormula_falsity hL hn]
        exact iff_of_true ((satisfies_truth hL hn).mpr hb) (not_satisfies_falsity hL hn)
    · intro n hn r args ha
      constructor
      · intro b hb
        rw [negateFormula_atom hL hn ha, satisfies_negAtom hL hn ha hb, satisfies_atom hL hn ha hb]
      · intro b hb
        rw [negateFormula_negAtom hL hn ha, satisfies_atom hL hn ha hb, satisfies_negAtom hL hn ha hb]
        exact not_not.symm
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro b hb
        rw [negateFormula_and hL hn hφ hψ,
          satisfies_or hL hn (negateFormula_mem hL hφ) (negateFormula_mem hL hψ) hb,
          satisfies_and hL hn hφ hψ hb, ihφ b hb, ihψ b hb]
        exact not_and_or.symm
      · intro b hb
        rw [negateFormula_or hL hn hφ hψ,
          satisfies_and hL hn (negateFormula_mem hL hφ) (negateFormula_mem hL hψ) hb,
          satisfies_or hL hn hφ hψ hb, ihφ b hb, ihψ b hb]
        exact not_or.symm
    · intro n hn φ hφ ih
      constructor
      · intro b hb
        rw [negateFormula_all hL hn hφ, satisfies_exists hL hn (negateFormula_mem hL hφ) hb,
          satisfies_all hL hn hφ hb]
        simp only [not_forall, exists_prop]
        apply exists_congr
        intro x
        apply and_congr_right
        intro hx
        exact ih _ (assignmentPrepend_mem_function hn hb hx)
      · intro b hb
        rw [negateFormula_exists hL hn hφ, satisfies_all hL hn (negateFormula_mem hL hφ) hb,
          satisfies_exists hL hn hφ hb]
        simp only [not_exists, not_and]
        apply forall_congr'
        intro x
        apply forall_congr'
        intro hx
        exact ih _ (assignmentPrepend_mem_function hn hb hx)
  exact hall n φ hφ b hb

theorem encodeSemiformula_neg {Λ : Language} {ξ : Type*} {L Γ : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V))
    (he : ∀ x, e x ∈ Γ) {n : ℕ} (φ : Semiformula Λ ξ n) :
    encodeSemiformula F R e (∼φ) = negateFormula L Γ (n : V) (encodeSemiformula F R e φ) := by
  have hmem : ∀ {n} (ψ : Semiformula Λ ξ n), encodeSemiformula F R e ψ ∈ formulaSet L Γ (n : V) :=
    fun ψ ↦ (mem_formulaSet_iff _ _ _ _).mpr (encodeSemiformula_mem_family hL F R e hF hR he ψ)
  have ha : ∀ n k (r : Λ.Rel k) (ts : Fin k → Semiterm Λ ξ n),
      IsAtomicArguments L Γ (n : V) (relationToken (R r))
        (standardTuple (fun i ↦ encodeSemiterm F e (ts i))) := by
    intro n k r ts
    refine Or.inr ⟨R r, (hR k r).1, rfl, ?_⟩
    rw [(hR k r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem hL F e hF he (ts i))
  induction φ with
  | verum => exact (negateFormula_truth hL (by simp) Γ).symm
  | falsum => exact (negateFormula_falsity hL (by simp) Γ).symm
  | rel r ts => exact (negateFormula_atom hL (by simp) (ha _ _ r ts)).symm
  | nrel r ts => exact (negateFormula_negAtom hL (by simp) (ha _ _ r ts)).symm
  | and φ ψ ihφ ihψ =>
    change orCode _ _ = negateFormula _ _ _ (andCode _ _)
    rw [negateFormula_and hL (by simp) (hmem φ) (hmem ψ)]
    exact congrArg₂ orCode ihφ ihψ
  | or φ ψ ihφ ihψ =>
    change andCode _ _ = negateFormula _ _ _ (orCode _ _)
    rw [negateFormula_or hL (by simp) (hmem φ) (hmem ψ)]
    exact congrArg₂ andCode ihφ ihψ
  | @all n φ ih =>
    change existsCode _ = negateFormula _ _ _ (allCode _)
    rw [negateFormula_all hL (by simp) (by simpa [num_succ_def] using hmem φ)]
    exact congrArg existsCode (by simpa only [num_succ_def, Semiformula.neg_eq] using ih)
  | @exs n φ ih =>
    change allCode _ = negateFormula _ _ _ (existsCode _)
    rw [negateFormula_exists hL (by simp) (by simpa [num_succ_def] using hmem φ)]
    exact congrArg allCode (by simpa only [num_succ_def, Semiformula.neg_eq] using ih)

end ZFVP
