import ZFVP.Syntax.NaturalLKCompleteness
import ZFVP.ModelTheory.GeneratedZFVPTheoryEquivalence

/-! A primitive recursive proof checker for the full generated ZF+VP theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev GeneratedTheoryCertificate := List (SetTheorySentence × ℕ) × LKCertificateData

def GeneratedTheoryProofCertificate (φ : SetTheorySentence) (p : GeneratedTheoryCertificate) : Prop :=
  (∀ row ∈ p.1, GeneratedAxiomCertificate row.1 row.2) ∧
    LKProofCertificate ((φ : SetTheoryProposition) :: ∼Sequent.embed (p.1.map Prod.fst)) p.2

instance (φ : SetTheorySentence) (p : GeneratedTheoryCertificate) :
    Decidable (GeneratedTheoryProofCertificate φ p) := by
  unfold GeneratedTheoryProofCertificate LKProofCertificate GeneratedAxiomCertificate
  infer_instance

theorem sentence_embed_primrec : Primrec (fun φ : SetTheorySentence ↦ (φ : SetTheoryProposition)) := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq (fun _ ↦ by simp)

theorem generatedTheoryProofCertificate_primrec :
    PrimrecPred (fun p : SetTheorySentence × GeneratedTheoryCertificate ↦ GeneratedTheoryProofCertificate p.1 p.2) := by
  have hrows : Primrec (fun p : SetTheorySentence × GeneratedTheoryCertificate ↦ p.2.1) := Primrec.fst.comp Primrec.snd
  have hΓ := Primrec.list_map hrows (Primrec.fst.comp Primrec.snd).to₂
  have hemb := Primrec.list_map hΓ (sentence_embed_primrec.comp Primrec.snd).to₂
  have hn := Primrec.list_map hemb ((syntacticFormula_neg_primrec 0).comp Primrec.snd).to₂
  have hC := Primrec.list_cons.comp (sentence_embed_primrec.comp Primrec.fst) hn
  have ha := generatedAxiomCertificate_primrec.forall_mem_list.comp hrows
  have hp := lkProofCertificate_primrec.comp (Primrec₂.pair.comp hC (Primrec.snd.comp Primrec.snd))
  exact (ha.and hp).of_eq (fun _ ↦ Iff.rfl)

theorem generatedAxiomListCertificate_exists {Γ : List SetTheorySentence}
    (hΓ : ∀ φ ∈ Γ, φ ∈ generatedZFVPTheory) :
    ∃ a : List (SetTheorySentence × ℕ), a.map Prod.fst = Γ ∧
      ∀ row ∈ a, GeneratedAxiomCertificate row.1 row.2 := by
  induction Γ with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons φ Γ ih =>
    obtain ⟨e, he⟩ := (generatedAxiomEnumeration_iff φ).mpr (hΓ φ (by simp))
    obtain ⟨a, ha, hax⟩ := ih (fun ψ hψ ↦ hΓ ψ (by simp [hψ]))
    refine ⟨(φ, e) :: a, by simp [ha], ?_⟩
    intro row hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact he
    · exact hax row hr

theorem generatedTheoryProofCertificate_iff (φ : SetTheorySentence) :
    (∃ p, GeneratedTheoryProofCertificate φ p) ↔ generatedZFVPTheory ⊢ φ := by
  constructor
  · rintro ⟨⟨a, p⟩, ha, hp⟩
    apply Theory.Proof.provable_iff.mpr
    refine ⟨a.map Prod.fst, ?_, LKCertified.sound ⟨p, hp⟩⟩
    intro ψ hψ
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hψ
    exact (generatedAxiomEnumeration_iff row.1).mp ⟨row.2, ha row hr⟩
  · intro h
    obtain ⟨Γ, hΓ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
    obtain ⟨a, ha, hax⟩ := generatedAxiomListCertificate_exists hΓ
    obtain ⟨p, hp, hpm⟩ := lkCertified_of_derivation d
    refine ⟨(a, p), hax, ?_⟩
    simpa only [LKProofCertificate, ha] using And.intro hp hpm

theorem externalZFVP_proofCertificate_iff (φ : SetTheorySentence) :
    (∃ p, GeneratedTheoryProofCertificate φ p) ↔ zfVPTheory ⊢ φ :=
  (generatedTheoryProofCertificate_iff φ).trans (generatedZFVPTheory_provable_iff φ)

theorem zfVPTheory_provable_re : REPred (fun φ : SetTheorySentence ↦ zfVPTheory ⊢ φ) :=
  generatedTheoryProofCertificate_primrec.computablePred.to_re.projection.of_eq externalZFVP_proofCertificate_iff

end ZFVP
