import Foundation.FirstOrder.Basic.PrimrecCoding
import ZFVP.ModelTheory.GeneratedZFVPTheory

/-! Primitive recursive natural-number decoding for the actual pure membership syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

instance membershipLanguage_primcodable : (ℒₛₑₜ).Primcodable where
  func := by
    exact (Primrec.const 0).of_eq (fun _ ↦ rfl)
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 < 2 then p.2 + 1 else 0 :=
      Primrec.ite
        (PrimrecPred.and (Primrec.eq.comp Primrec.fst (Primrec.const 2))
          (Primrec.nat_lt.comp Primrec.snd (Primrec.const 2)))
        (Primrec.succ.comp Primrec.snd) (Primrec.const 0)
    refine h.of_eq ?_
    rintro ⟨k, e⟩
    match k, e with
    | 0, _ => simp [Encodable.decode]
    | 1, _ => simp [Encodable.decode]
    | 2, 0 => rfl
    | 2, 1 => rfl
    | 2, _ + 2 => simp [Encodable.decode]
    | _ + 3, _ => simp [Encodable.decode]

theorem membershipFormula_decode_primrec :
    Primrec₂ (fun n e : ℕ ↦ Encodable.encode (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e)) :=
  Semiformula.encode_ofNat_primrec

theorem membershipTerm_decode_primrec :
    Primrec₂ (fun n e : ℕ ↦ Encodable.encode (Semiterm.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e)) :=
  Semiterm.encode_ofNat_primrec

theorem membershipFormula_encode_decode {n : ℕ} (φ : SetTheorySemisentence n) :
    (Encodable.decode (Encodable.encode φ) : Option (SetTheorySemisentence n)) = some φ :=
  Encodable.encodek φ

def IsStandardMembershipCode (n e : ℕ) : Prop :=
  (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e).isSome

theorem isStandardMembershipCode_primrec : PrimrecPred (fun p : ℕ × ℕ ↦ IsStandardMembershipCode p.1 p.2) := by
  have h := (Primrec.eq.comp membershipFormula_decode_primrec (Primrec.const 0)).not
  refine h.of_eq ?_
  intro p
  simp only [IsStandardMembershipCode]
  cases Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) p.1 p.2 <;> simp [Encodable.encode]

theorem isStandardMembershipCode_iff (n e : ℕ) :
    IsStandardMembershipCode n e ↔ ∃ φ : SetTheorySemisentence n,
      Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e = some φ := by
  simp [IsStandardMembershipCode, Option.isSome_iff_exists]

end ZFVP
