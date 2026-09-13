import ZFVP.Syntax.NaturalPrefixRenaming

/-! Unused surrounding contexts do not alter the natural-number syntax encoding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem encodeNatTerm_sameIndices {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = i.val) (t : Semiterm ℒₛₑₜ Empty n) :
    Encodable.encode (σ t) = Encodable.encode t := by
  cases t with
  | bvar i =>
    obtain ⟨j, hj, he⟩ := hσ i
    rw [hj]
    change Nat.pair 0 j.val + 1 = Nat.pair 0 i.val + 1
    rw [he]
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem encodeNatFormula_sameIndices {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = i.val) (φ : SetTheorySemisentence n) :
    Encodable.encode (σ ▹ φ) = Encodable.encode φ := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts => simp only [Semiformula.rew_rel, Semiformula.encode_rel, encodeNatTerm_sameIndices σ hσ]
  | nrel r ts => simp only [Semiformula.rew_nrel, Semiformula.encode_nrel, encodeNatTerm_sameIndices σ hσ]
  | and φ ψ ihφ ihψ =>
    exact congrArg₂ (fun x y ↦ Nat.pair 4 (Nat.pair x y) + 1) (ihφ σ hσ) (ihψ σ hσ)
  | or φ ψ ihφ ihψ =>
    exact congrArg₂ (fun x y ↦ Nat.pair 5 (Nat.pair x y) + 1) (ihφ σ hσ) (ihψ σ hσ)
  | all φ ih => exact congrArg (fun x ↦ Nat.pair 6 x + 1) (ih σ.q (sameIndices_q σ hσ))
  | exs φ ih => exact congrArg (fun x ↦ Nat.pair 7 x + 1) (ih σ.q (sameIndices_q σ hσ))

end ZFVP
