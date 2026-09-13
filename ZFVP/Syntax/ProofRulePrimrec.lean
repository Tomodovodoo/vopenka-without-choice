import ZFVP.Syntax.NaturalProofRewritingPrimrec
import ZFVP.Syntax.GeneratedAxiomPrimrec

/-! Primitive recursive operations used by Foundation's first-order proof rules. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem proofRewNatFormula_shift (φ : SetTheoryProposition) :
    proofRewNatFormula 0 0 (Encodable.encode φ) = Encodable.encode φ.shift := by
  apply proofRewNatFormula_encode 0 0 Rew.shift
  intro t
  cases t with
  | bvar i => exact i.elim0
  | fvar i => change proofRewNatTerm 0 0 (Nat.pair 1 i + 1) = Nat.pair 1 (i + 1) + 1; simp [proofRewNatTerm]
  | func f _ => exact Empty.elim f

theorem proofRewNatFormula_free (φ : Semiproposition ℒₛₑₜ 1) :
    proofRewNatFormula 1 0 (Encodable.encode φ) = Encodable.encode φ.free := by
  apply proofRewNatFormula_encode 1 0 (Rew.free (n := 0))
  intro t
  cases t with
  | bvar i =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rw [Rew.free_bvar_last_zero]
    change proofRewNatTerm 1 0 (Nat.pair 0 0 + 1) = Nat.pair 1 0 + 1
    simp [proofRewNatTerm]
  | fvar i => change proofRewNatTerm 1 0 (Nat.pair 1 i + 1) = Nat.pair 1 (i + 1) + 1; simp [proofRewNatTerm]
  | func f _ => exact Empty.elim f

theorem proofRewNatFormula_subst (k : ℕ) (φ : Semiproposition ℒₛₑₜ 1) :
    proofRewNatFormula (k + 2) 0 (Encodable.encode φ) = Encodable.encode (φ/[&k] : SetTheoryProposition) := by
  apply proofRewNatFormula_encode (k + 2) 0 (Rew.subst ![&k])
  intro t
  cases t with
  | bvar i =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    change proofRewNatTerm (k + 2) 0 (Nat.pair 0 0 + 1) = Nat.pair 1 k + 1
    simp [proofRewNatTerm]
  | fvar i => change proofRewNatTerm (k + 2) 0 (Nat.pair 1 i + 1) = Nat.pair 1 i + 1; simp [proofRewNatTerm]
  | func f _ => exact Empty.elim f

theorem proposition_shift_primrec : Primrec (fun φ : SetTheoryProposition ↦ φ.shift) := by
  apply Primrec.encode_iff.mp
  exact (proofRewNatFormula_primrec.comp (Primrec.const 0)
    (Primrec₂.pair.comp (Primrec.const 0) Primrec.encode)).of_eq proofRewNatFormula_shift

theorem proposition_free_primrec : Primrec (fun φ : Semiproposition ℒₛₑₜ 1 ↦ φ.free) := by
  apply Primrec.encode_iff.mp
  exact (proofRewNatFormula_primrec.comp (Primrec.const 1)
    (Primrec₂.pair.comp (Primrec.const 0) Primrec.encode)).of_eq proofRewNatFormula_free

theorem proposition_subst_primrec : Primrec₂ (fun (k : ℕ) (φ : Semiproposition ℒₛₑₜ 1) ↦ (φ/[&k] : SetTheoryProposition)) := by
  apply Primrec.encode_iff.mp
  exact (proofRewNatFormula_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
    (Primrec₂.pair.comp (Primrec.const 0) (Primrec.encode.comp Primrec.snd))).of_eq
      (fun p ↦ proofRewNatFormula_subst p.1 p.2)

theorem syntacticFormula_neg_primrec (n : ℕ) : Primrec (fun φ : Semiproposition ℒₛₑₜ n ↦ ∼φ) :=
  Primrec.encode_iff.mp ((negateNatFormula_primrec.comp Primrec.encode).of_eq negateNatFormula_encode)

theorem proposition_and_primrec : Primrec₂ (fun φ ψ : SetTheoryProposition ↦ φ ⋏ ψ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)))).of_eq (fun _ ↦ rfl)

theorem proposition_or_primrec : Primrec₂ (fun φ ψ : SetTheoryProposition ↦ φ ⋎ ψ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)))).of_eq (fun _ ↦ rfl)

theorem proposition_all_primrec : Primrec (fun φ : Semiproposition ℒₛₑₜ 1 ↦ ∀¹ φ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) Primrec.encode)).of_eq (fun _ ↦ rfl)

theorem proposition_exs_primrec : Primrec (fun φ : Semiproposition ℒₛₑₜ 1 ↦ ∃¹ φ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 7) Primrec.encode)).of_eq (fun _ ↦ rfl)

end ZFVP
