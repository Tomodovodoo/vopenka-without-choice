import ZFVP.Syntax.NaturalFormulaNegation

/-! Primitive recursive quantifier constructors and full universal closure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def allNatFormula (k e : ℕ) : ℕ := (fun c ↦ Nat.pair 6 c + 1)^[k] e

theorem allNatFormula_succ (k e : ℕ) : allNatFormula (k + 1) e = allNatFormula k (Nat.pair 6 e + 1) :=
  Function.iterate_succ_apply _ _ _

theorem allNatFormula_encode {n : ℕ} (φ : SetTheorySemisentence n) :
    allNatFormula n (Encodable.encode φ) = Encodable.encode (∀¹* φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allNatFormula_succ]
    exact ih (∀¹ φ)

theorem allNatFormula_primrec : Primrec₂ allNatFormula :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) Primrec.snd))

theorem membershipFormula_all_primrec (n : ℕ) : Primrec (fun φ : SetTheorySemisentence (n + 1) ↦ ∀¹ φ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) Primrec.encode)).of_eq
    (fun φ ↦ (Semiformula.encode_all φ).symm)

theorem membershipFormula_exs_primrec (n : ℕ) : Primrec (fun φ : SetTheorySemisentence (n + 1) ↦ ∃¹ φ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 7) Primrec.encode)).of_eq
    (fun φ ↦ (Semiformula.encode_ex φ).symm)

def IsCanonicalMembershipCode (n e : ℕ) : Prop :=
  Encodable.encode (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e) = e + 1

theorem isCanonicalMembershipCode_primrec :
    PrimrecPred (fun p : ℕ × ℕ ↦ IsCanonicalMembershipCode p.1 p.2) :=
  Primrec.eq.comp membershipFormula_decode_primrec (Primrec.succ.comp Primrec.snd)

theorem isCanonicalMembershipCode_iff (n e : ℕ) :
    IsCanonicalMembershipCode n e ↔ ∃ φ : SetTheorySemisentence n, Encodable.encode φ = e := by
  constructor
  · intro h
    unfold IsCanonicalMembershipCode at h
    cases he : Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e with
    | none => simp [he, Encodable.encode] at h
    | some φ =>
      refine ⟨φ, ?_⟩
      simpa [he, Encodable.encode] using h
  · rintro ⟨φ, rfl⟩
    change Encodable.encode (Encodable.decode (Encodable.encode φ) : Option (SetTheorySemisentence n)) = _
    rw [Encodable.encodek]
    rfl

end ZFVP
