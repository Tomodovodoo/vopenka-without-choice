import ZFVP.Syntax.GeneratedTheoryProofCertificate

/-! A natural-number proof predicate for exactly the external ZF+VP theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def checkNaturalZFVPProof (f e : ℕ) : Bool :=
  (Encodable.decode f : Option SetTheorySentence).elim false fun φ ↦
    (Encodable.decode e : Option GeneratedTheoryCertificate).elim false fun p ↦
      decide (GeneratedTheoryProofCertificate φ p)

def NaturalZFVPProof (f e : ℕ) : Prop := checkNaturalZFVPProof f e = true

theorem checkNaturalZFVPProof_primrec : Primrec₂ checkNaturalZFVPProof := by
  open Primrec in
  have hinner : Primrec (fun p : (ℕ × ℕ) × SetTheorySentence ↦
      (Encodable.decode p.1.2 : Option GeneratedTheoryCertificate).elim false fun c ↦
        decide (GeneratedTheoryProofCertificate p.2 c)) := by
    have hcheck : Primrec (fun p : ((ℕ × ℕ) × SetTheorySentence) × GeneratedTheoryCertificate ↦
        decide (GeneratedTheoryProofCertificate p.1.2 p.2)) :=
      generatedTheoryProofCertificate_primrec.decide.comp
        (Primrec₂.pair.comp (snd.comp fst) snd)
    exact (option_casesOn (Primrec.decode.comp (snd.comp fst)) (const false) hcheck.to₂).of_eq
      (fun _ ↦ by cases Encodable.decode (α := GeneratedTheoryCertificate) _ <;> rfl)
  exact (Primrec.option_casesOn (Primrec.decode.comp Primrec.fst) (Primrec.const false) hinner.to₂).of_eq
    (fun p ↦ by unfold checkNaturalZFVPProof; cases Encodable.decode (α := SetTheorySentence) p.1 <;> rfl)

theorem naturalZFVPProof_primrec : PrimrecRel NaturalZFVPProof :=
  Primrec.eq.comp checkNaturalZFVPProof_primrec (Primrec.const true)

theorem naturalZFVPProof_iff (f e : ℕ) : NaturalZFVPProof f e ↔
    ∃ φ p, (Encodable.decode f : Option SetTheorySentence) = some φ ∧
      (Encodable.decode e : Option GeneratedTheoryCertificate) = some p ∧
      GeneratedTheoryProofCertificate φ p := by
  simp only [NaturalZFVPProof, checkNaturalZFVPProof]
  cases Encodable.decode (α := SetTheorySentence) f <;>
    cases Encodable.decode (α := GeneratedTheoryCertificate) e <;> simp

theorem naturalZFVPProof_encode_iff (φ : SetTheorySentence) :
    (∃ e, NaturalZFVPProof (Encodable.encode φ) e) ↔ zfVPTheory ⊢ φ := by
  rw [← externalZFVP_proofCertificate_iff]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨ψ, p, hψ, _, hp⟩ := (naturalZFVPProof_iff _ _).mp he
    have h : ψ = φ := by simpa using hψ.symm
    exact ⟨p, h ▸ hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨Encodable.encode p, (naturalZFVPProof_iff _ _).mpr
      ⟨φ, p, Encodable.encodek _, Encodable.encodek _, hp⟩⟩

def NaturalZFVPConsistent : Prop :=
  ∀ e, ¬ NaturalZFVPProof (Encodable.encode (⊥ : SetTheorySentence)) e

theorem naturalZFVPConsistent_iff : NaturalZFVPConsistent ↔ Entailment.Consistent zfVPTheory := by
  rw [Entailment.consistent_iff_unprovable_bot]
  simpa only [NaturalZFVPConsistent, not_exists] using not_congr (naturalZFVPProof_encode_iff (⊥ : SetTheorySentence))

end ZFVP
