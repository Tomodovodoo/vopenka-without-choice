import ZFVP.Syntax.MembershipEncodingRewriting

/-! Formula codes do not record unused surrounding variable contexts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sameIndices_q {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = i.val) :
    ∀ i, ∃ j, σ.q (.bvar i) = .bvar j ∧ j.val = i.val := by
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact ⟨0, rfl, rfl⟩
  · obtain ⟨j, hj, he⟩ := hσ i
    exact ⟨j.succ, by simp [Rew.q_bvar_succ, hj], by simp [he]⟩

theorem encodeMembershipTerm_sameIndices {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = i.val)
    (t : Semiterm ℒₛₑₜ Empty n) :
    encodeSemiterm (V := V) (fun {k} ↦ membershipFunctionSymbol (k := k)) Empty.elim (σ t) =
      encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (k := k)) Empty.elim t := by
  cases t with
  | bvar i => obtain ⟨j, hj, he⟩ := hσ i; simp [hj, encodeSemiterm, he]
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem encodeMembershipFormula_sameIndices {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = i.val)
    (φ : SetTheorySemisentence n) :
    encodeMembershipFormula (V := V) (σ ▹ φ) = encodeMembershipFormula φ := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    simp only [Semiformula.rew_rel, encodeMembershipFormula, encodeSemiformula,
      encodeMembershipTerm_sameIndices σ hσ]
  | nrel r ts =>
    simp only [Semiformula.rew_nrel, encodeMembershipFormula, encodeSemiformula,
      encodeMembershipTerm_sameIndices σ hσ]
  | and φ ψ ihφ ihψ => exact congrArg₂ andCode (ihφ σ hσ) (ihψ σ hσ)
  | or φ ψ ihφ ihψ => exact congrArg₂ orCode (ihφ σ hσ) (ihψ σ hσ)
  | all φ ih => exact congrArg allCode (ih σ.q (sameIndices_q σ hσ))
  | exs φ ih => exact congrArg existsCode (ih σ.q (sameIndices_q σ hσ))

theorem encodeMembershipFormula_closed_rew {m : ℕ} (σ : Rew ℒₛₑₜ Empty 0 Empty m)
    (φ : SetTheorySentence) :
    encodeMembershipFormula (V := V) (σ ▹ φ) = encodeMembershipFormula φ :=
  encodeMembershipFormula_sameIndices σ (fun i ↦ Fin.elim0 i) φ

@[simp] theorem encodeMembershipFormula_finiteVariableClosure_embed (k : ℕ) (φ : SetTheorySentence) :
    encodeMembershipFormula (V := V) (finiteVariableClosure k (φ : SetTheoryProposition)) =
      encodeMembershipFormula φ := by
  rw [finiteVariableClosure_embed k φ (Rew.bind Fin.elim0 Empty.elim)]
  exact encodeMembershipFormula_closed_rew _ φ

end ZFVP
