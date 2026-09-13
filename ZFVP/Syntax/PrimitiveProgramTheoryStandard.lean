import ZFVP.Syntax.PrimitiveProgramGeneratedStandard
import ZFVP.Syntax.PrimitiveProgramTheoryProof
import ZFVP.Syntax.PrimitiveProgramLKStandardCertificate
import ZFVP.Syntax.GeneratedTheoryProofCertificate

/-! Standard typed derivations of ZF+VP have certificates accepted by the explicit program. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem generatedAxiomRowsCheck_encode (z : ℕ) (rows : List (SetTheorySentence × ℕ)) :
    generatedAxiomRowsCheck.eval (Nat.pair z (Encodable.encode rows)) = 1 ↔
      ∀ row ∈ rows, generatedAxiomCheck.eval (Nat.pair (Encodable.encode row.1) row.2) = 1 := by
  rw [generatedAxiomRowsCheck, listAll_encode_iff]
  simp [← evalArithmetic_nat, ← arithmeticPair_nat, Encodable.encode_prod_val]

theorem negatedAxiomRow_encode (z : ℕ) (row : SetTheorySentence × ℕ) :
    negatedAxiomRow.eval (Nat.pair z (Encodable.encode row)) =
      Encodable.encode (∼(row.1 : SetTheoryProposition)) := by
  obtain ⟨φ, w⟩ := row
  have h := evalArithmetic_negatedAxiomRow (z : ℕ) (Encodable.encode (φ, w) : ℕ)
  simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticPiOne_nat,
    Encodable.encode_prod_val, Nat.unpair_pair, Encodable.encode_nat] at h
  rw [Encodable.encode_prod_val, Encodable.encode_nat, h, negateCode_encode]
  simp

theorem generatedTheorySequent_encode (φ : SetTheorySentence) (rows : List (SetTheorySentence × ℕ)) :
    generatedTheorySequent.eval (Nat.pair (Encodable.encode φ) (Encodable.encode rows)) =
      Encodable.encode ((φ : SetTheoryProposition) :: ∼Sequent.embed (rows.map Prod.fst)) := by
  have h := evalArithmetic_generatedTheorySequent (Encodable.encode φ : ℕ) (Encodable.encode rows : ℕ)
  simp only [arithmeticPair_nat, evalArithmetic_nat] at h
  rw [h, listMap_encode negatedAxiomRow (fun row ↦ ∼(row.1 : SetTheoryProposition)) 0
    (negatedAxiomRow_encode 0)]
  simp [Sequent.embed, List.map_map, Encodable.encode_list_cons]
  change rows.map _ = (rows.map _).map (∼·)
  rw [List.map_map]
  rfl

theorem generatedTheoryProofCheck_encode (φ : SetTheorySentence) (p : GeneratedTheoryCertificate) :
    generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) (Encodable.encode p)) = 1 ↔
      (∀ row ∈ p.1, generatedAxiomCheck.eval (Nat.pair (Encodable.encode row.1) row.2) = 1) ∧
        LKProofCertificate ((φ : SetTheoryProposition) :: ∼Sequent.embed (p.1.map Prod.fst)) p.2 := by
  obtain ⟨rows, cert⟩ := p
  have h := evalArithmetic_generatedTheoryProofCheck (Encodable.encode φ : ℕ)
    (Encodable.encode rows : ℕ) (Encodable.encode cert : ℕ)
  simp only [arithmeticPair_nat, evalArithmetic_nat] at h
  rw [formulaCheck_encode false Empty.elim φ, generatedAxiomRowsCheck_encode,
    generatedTheorySequent_encode, lkProofCheck_encode] at h
  simpa only [Encodable.encode_prod_val, true_and] using h

theorem generatedAxiomProgramList_exists {Γ : List SetTheorySentence}
    (hΓ : ∀ φ ∈ Γ, φ ∈ generatedZFVPTheory) :
    ∃ rows : List (SetTheorySentence × ℕ), rows.map Prod.fst = Γ ∧
      ∀ row ∈ rows, generatedAxiomCheck.eval (Nat.pair (Encodable.encode row.1) row.2) = 1 := by
  induction Γ with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons φ Γ ih =>
    obtain ⟨e, he⟩ := generatedAxiomCheck_complete (hΓ φ (by simp))
    obtain ⟨rows, hr, hrows⟩ := ih (fun ψ hψ ↦ hΓ ψ (by simp [hψ]))
    refine ⟨(φ, e) :: rows, by simp [hr], ?_⟩
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · exact he
    · exact hrows row hrow

theorem generatedTheoryProofCheck_complete {φ : SetTheorySentence} (hφ : generatedZFVPTheory ⊢ φ) :
    ∃ p : GeneratedTheoryCertificate,
      generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) (Encodable.encode p)) = 1 := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hφ
  obtain ⟨rows, hr, hrows⟩ := generatedAxiomProgramList_exists hΓ
  obtain ⟨p, hp, hpm⟩ := lkCertified_of_derivation d
  refine ⟨(rows, p), (generatedTheoryProofCheck_encode φ (rows, p)).mpr ⟨hrows, ?_⟩⟩
  simpa only [LKProofCertificate, hr] using And.intro hp hpm

theorem externalZFVP_programProof_complete {φ : SetTheorySentence} (hφ : zfVPTheory ⊢ φ) :
    ∃ p : ℕ, generatedTheoryProofCheck.eval (Nat.pair (Encodable.encode φ) p) = 1 := by
  obtain ⟨p, hp⟩ := generatedTheoryProofCheck_complete ((generatedZFVPTheory_provable_iff φ).mpr hφ)
  exact ⟨Encodable.encode p, hp⟩

end PrimitiveProgram
end ZFVP
