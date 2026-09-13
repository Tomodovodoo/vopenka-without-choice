import ZFVP.Syntax.PrimitiveProgramGeneratedRaw
import ZFVP.Syntax.PrimitiveProgramLKRawCertificate
import ZFVP.Syntax.PrimitiveProgramTheoryStandard

/-! Raw standard certificates prove exactly the sentences of the intended ZF+VP theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

def rawSentence (c : ℕ) : SetTheorySentence := (Semiformula.ofNat 0 c).getD ⊥

@[simp] theorem rawSentence_encode (φ : SetTheorySentence) : rawSentence (Encodable.encode φ) = φ := by
  simp only [rawSentence, (RawFormulaCode.encode φ).ofNat, Option.getD_some]

def rawAxiomSentences (rows : ℕ) : List SetTheorySentence :=
  (Nat.natToList rows).map (fun row ↦ rawSentence row.unpair.1)

theorem generatedAxiomRowsCheck_natToList (z rows : ℕ) :
    generatedAxiomRowsCheck.eval (Nat.pair z rows) = 1 ↔
      ∀ row ∈ Nat.natToList rows, generatedAxiomCheck.eval row = 1 := by
  rw [generatedAxiomRowsCheck, listAll_natToList]
  simp [← evalArithmetic_nat, ← arithmeticPair_nat]

theorem generatedAxiomCheck_rawSentence (row : ℕ) (h : generatedAxiomCheck.eval row = 1) :
    row.unpair.1 = Encodable.encode (rawSentence row.unpair.1) ∧
      rawSentence row.unpair.1 ∈ generatedZFVPTheory := by
  obtain ⟨c, e, rfl⟩ := rawPair_cases row
  rw [generatedAxiomCheck_nat] at h
  obtain ⟨φ, hφ, hm⟩ := generatedAxiomProgram_sound_nat h
  simpa only [Nat.unpair_pair, hφ, rawSentence_encode, true_and, eq_self] using hm

theorem rawAxiomSentences_mem {rows : ℕ} (h : generatedAxiomRowsCheck.eval (Nat.pair 0 rows) = 1) :
    ∀ φ ∈ rawAxiomSentences rows, φ ∈ generatedZFVPTheory := by
  intro φ hφ
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hφ
  exact (generatedAxiomCheck_rawSentence row ((generatedAxiomRowsCheck_natToList 0 rows).mp h row hrow)).2

theorem generatedTheorySequent_raw (φ : SetTheorySentence) (rows : ℕ)
    (h : generatedAxiomRowsCheck.eval (Nat.pair 0 rows) = 1) :
    rawSequent (generatedTheorySequent.eval (Nat.pair (Encodable.encode φ) rows)) =
      (φ : SetTheoryProposition) :: ∼Sequent.embed (rawAxiomSentences rows) := by
  have he := evalArithmetic_generatedTheorySequent (Encodable.encode φ : ℕ) rows
  simp only [arithmeticPair_nat, evalArithmetic_nat, OfNat.ofNat, One.one, Zero.zero] at he
  rw [he, rawSequent_cons, rawSequent_listMap]
  have hf : rawFormula 0 (Encodable.encode φ) = (φ : SetTheoryProposition) := by
    simpa using rawFormula_encode (φ : SetTheoryProposition)
  rw [hf]
  apply congrArg (List.cons (φ : SetTheoryProposition))
  simp only [rawAxiomSentences, Sequent.embed, List.map_map]
  change (Nat.natToList rows).map _ = ((Nat.natToList rows).map _).map (∼·)
  rw [List.map_map]
  apply List.map_congr_left
  intro row hrow
  have hc := (generatedAxiomCheck_rawSentence row ((generatedAxiomRowsCheck_natToList 0 rows).mp h row hrow)).1
  have hn := evalArithmetic_negatedAxiomRow (0 : ℕ) row
  simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticPiOne_nat] at hn
  rw [hn, hc, negateCode_encode]
  have hx := rawFormula_encode ((∼rawSentence row.unpair.1 : SetTheorySentence) : SetTheoryProposition)
  rw [Semiformula.encode_emb] at hx
  simpa only [LogicalConnective.HomClass.map_neg, Function.comp_apply, rawSentence_encode] using hx

theorem generatedTheoryProofCheck_sound_nat (φ : SetTheorySentence) (p : ℕ)
    (hcheck : generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) p) = 1) :
    generatedZFVPTheory ⊢ φ := by
  obtain ⟨rows, cert, rfl⟩ := rawPair_cases p
  have he := evalArithmetic_generatedTheoryProofCheck (Encodable.encode φ : ℕ) rows cert
  simp only [arithmeticPair_nat, evalArithmetic_nat] at he
  obtain ⟨_, hrows, hlk⟩ := he.mp hcheck
  have hd := lkProofCheck_raw_sound _ cert hlk
  rw [generatedTheorySequent_raw φ rows hrows] at hd
  exact Theory.Proof.provable_iff.mpr ⟨rawAxiomSentences rows, rawAxiomSentences_mem hrows, hd⟩

theorem generatedTheory_programProof_iff (φ : SetTheorySentence) :
    (∃ p : ℕ, generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) p) = 1) ↔ generatedZFVPTheory ⊢ φ := by
  constructor
  · rintro ⟨p, hp⟩
    exact generatedTheoryProofCheck_sound_nat φ p hp
  · intro h
    obtain ⟨p, hp⟩ := generatedTheoryProofCheck_complete h
    exact ⟨Encodable.encode p, hp⟩

theorem externalZFVP_programProof_iff (φ : SetTheorySentence) :
    (∃ p : ℕ, generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) p) = 1) ↔ zfVPTheory ⊢ φ :=
  (generatedTheory_programProof_iff φ).trans (generatedZFVPTheory_provable_iff φ)

end ZFVP
