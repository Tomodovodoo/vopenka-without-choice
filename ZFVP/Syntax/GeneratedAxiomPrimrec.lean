import ZFVP.Syntax.TailTemplatePrimrec
import ZFVP.Syntax.GeneratedAxiomEnumeration

/-! The complete generated ZF+VP axiom enumeration is primitive recursive. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem MembershipTemplate.closedTailEnumeration_primrec {a : ℕ} (t : MembershipTemplate a 0) :
    Primrec₂ (fun k e : ℕ ↦ Encodable.encode
      ((Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) (k + a) e).map
        (fun φ ↦ ∀¹* t.instantiateTail k φ))) := by
  have hc : Primrec (fun p : ℕ × ℕ ↦ Encodable.encode
      (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) (p.1 + a) p.2)) :=
    membershipFormula_decode_primrec.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const a)) Primrec.snd
  have ht := t.compileTailNat_primrec.comp Primrec.fst (Primrec.nat_sub.comp hc (Primrec.const 1))
  have h := Primrec.ite (Primrec.eq.comp hc (Primrec.const 0)) (Primrec.const 0)
    (Primrec.succ.comp (allNatFormula_primrec.comp Primrec.fst ht))
  refine h.of_eq ?_
  rintro ⟨k, e⟩
  cases he : Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) (k + a) e with
  | none => simp [he, Encodable.encode]
  | some φ =>
    simp only [he, Option.map_some]
    change (if Encodable.encode φ + 1 = 0 then 0 else
      allNatFormula k (t.compileTailNat k (Encodable.encode φ + 1 - 1)) + 1) =
        Encodable.encode (∀¹* t.instantiateTail k φ) + 1
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [t.compileTailNat_encode φ, allNatFormula_encode]

theorem generatedAxiomAt_encode_primrec :
    Primrec (fun p : ℕ × (ℕ × ℕ) ↦ Encodable.encode (generatedAxiomAt p.1 p.2.1 p.2.2)) := by
  have hs : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ Encodable.encode (generatedAxiomAt 8 p.2.1 p.2.2)) :=
    separationTemplate.closedTailEnumeration_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ Encodable.encode (generatedAxiomAt 9 p.2.1 p.2.2)) :=
    replacementTemplate.closedTailEnumeration_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ Encodable.encode
      ((Encodable.decode p.2.2 : Option (SetTheorySemisentence 2)).map (fun φ ↦ vopenkaTemplate.instantiate φ))) :=
    Primrec.encode.comp (Primrec.option_map (Primrec.decode.comp (Primrec.snd.comp Primrec.snd))
      (vopenkaTemplate.instantiate_primrec.comp Primrec.snd))
  have h := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const (Encodable.encode (some Axiom.empty)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) (Primrec.const (Encodable.encode (some Axiom.extentionality)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) (Primrec.const (Encodable.encode (some Axiom.pairing)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3)) (Primrec.const (Encodable.encode (some Axiom.union)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4)) (Primrec.const (Encodable.encode (some Axiom.power)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5)) (Primrec.const (Encodable.encode (some Axiom.infinity)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6)) (Primrec.const (Encodable.encode (some Axiom.foundation)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7)) (Primrec.const (Encodable.encode (some equalityBasisSentence)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 8)) hs
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9)) hr
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 10)) hv (Primrec.const 0)))))))))))
  refine h.of_eq ?_
  rintro ⟨tag, k, e⟩
  match tag with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => simp [generatedAxiomAt] <;> rfl
  | n + 11 => simp [generatedAxiomAt]

theorem generatedAxiomEnumeration_primrec : Primrec generatedAxiomEnumeration := by
  apply Primrec.encode_iff.mp
  exact (generatedAxiomAt_encode_primrec.comp
    (Primrec₂.pair.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).of_eq (fun _ ↦ rfl)

def GeneratedAxiomCertificate (φ : SetTheorySentence) (e : ℕ) : Prop :=
  generatedAxiomEnumeration e = some φ

theorem generatedAxiomCertificate_primrec :
    PrimrecPred (fun p : SetTheorySentence × ℕ ↦ GeneratedAxiomCertificate p.1 p.2) :=
  Primrec.eq.comp (generatedAxiomEnumeration_primrec.comp Primrec.snd)
    (Primrec.option_some.comp Primrec.fst)

theorem generatedZFVPTheory_re : REPred (fun φ : SetTheorySentence ↦ φ ∈ generatedZFVPTheory) :=
  generatedAxiomCertificate_primrec.computablePred.to_re.projection.of_eq generatedAxiomEnumeration_iff

end ZFVP
