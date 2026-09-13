import ZFVP.Syntax.PrimitiveProgramLKNumerals
import ZFVP.Syntax.PrimitiveProgramTheoryProof

/-! Combining the axiom lists and LK certificates of accepted theory proofs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_listMap_append (f : PrimitiveProgram) (z xs ys : M) :
    (listMap f).evalArithmetic (Arithmetic.pair z (listAppend.evalArithmetic (Arithmetic.pair ys xs))) =
      listAppend.evalArithmetic (Arithmetic.pair
        ((listMap f).evalArithmetic (Arithmetic.pair z ys))
        ((listMap f).evalArithmetic (Arithmetic.pair z xs))) := by
  induction xs using ISigma1.sigma1_order_induction
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp
    · rw [evalArithmetic_listAppend_cons, evalArithmetic_listMap_cons,
        evalArithmetic_listMap_cons, evalArithmetic_listAppend_cons,
        ih tail (lt_succ_iff_le.mpr (le_pair_right x tail))]

theorem evalArithmetic_generatedAxiomRowsCheck_append (xs ys : M) :
    generatedAxiomRowsCheck.evalArithmetic
      (Arithmetic.pair 0 (listAppend.evalArithmetic (Arithmetic.pair ys xs))) = 1 ↔
      generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair 0 xs) = 1 ∧
        generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair 0 ys) = 1 :=
  evalArithmetic_listAll_append_iff _ _ _ _

theorem ProgramLKProvable.of_mem_iff {C D : M} (hD : ProgramLKProvable D)
    (he : ∀ x, listMember.evalArithmetic (Arithmetic.pair x D) = 1 ↔
      listMember.evalArithmetic (Arithmetic.pair x C) = 1) : ProgramLKProvable C := by
  have hv := hD.valid
  change (listAll (formulaCheck true)).evalArithmetic (Arithmetic.pair 0 D) = 1 at hv
  apply hD.weaken
  · change (listAll (formulaCheck true)).evalArithmetic (Arithmetic.pair 0 C) = 1
    rw [evalArithmetic_listAll_mem_iff] at hv ⊢
    exact fun x hx ↦ hv x ((he x).mpr hx)
  · rw [evalArithmetic_listSubset_mem_iff]
    exact fun x hx ↦ (he x).mp hx

theorem ProgramLKProvable.contextual_modusPonens {imp φ ψ Γ Δ : M}
    (hlog : ProgramLKProvable (Arithmetic.pair (negateCode.evalArithmetic imp)
      (Arithmetic.pair (negateCode.evalArithmetic φ) (Arithmetic.pair ψ 0 + 1) + 1) + 1))
    (himp : ProgramLKProvable (Arithmetic.pair imp Γ + 1))
    (hφ : ProgramLKProvable (Arithmetic.pair φ Δ + 1)) :
    ProgramLKProvable (Arithmetic.pair ψ (listAppend.evalArithmetic (Arithmetic.pair Δ Γ)) + 1) := by
  have h₁ := himp.cut hlog
  have h₂ : ProgramLKProvable (Arithmetic.pair (negateCode.evalArithmetic φ)
      (Arithmetic.pair ψ Γ + 1) + 1) := h₁.of_mem_iff (by
    intro x
    simp only [evalArithmetic_listMember_append_iff, evalArithmetic_listMember_cons_iff,
      evalArithmetic_listMember_zero_iff]
    tauto)
  exact (hφ.cut h₂).of_mem_iff (by
    intro x
    simp only [evalArithmetic_listMember_append_iff, evalArithmetic_listMember_cons_iff]
    tauto)

theorem derivation_modusPonens_sequent (φ ψ : Proposition ℒₛₑₜ) :
    Nonempty (Derivation [∼(φ 🡒 ψ), ∼φ, ψ]) := by
  have hp : Derivation [φ, ∼φ, ψ] := (Derivation.eta φ).contra (by simp)
  have hq : Derivation [∼ψ, ∼φ, ψ] := (Derivation.eta ψ).contra (by simp)
  exact ⟨(hp.and hq).cast (by simp [Semiformula.imp_eq])⟩

theorem programLKProvable_modusPonens_sequent (φ ψ : SetTheorySentence) :
    ProgramLKProvable (Arithmetic.pair
      (negateCode.evalArithmetic (Encodable.encode (φ 🡒 ψ) : M))
      (Arithmetic.pair (negateCode.evalArithmetic (Encodable.encode φ : M))
        (Arithmetic.pair (Encodable.encode ψ : M) 0 + 1) + 1) + 1) := by
  have h := programLKProvable_of_derivation (M := M)
    [∼(Rewriting.emb φ 🡒 Rewriting.emb ψ), ∼Rewriting.emb φ, Rewriting.emb ψ]
    (derivation_modusPonens_sequent (Rewriting.emb φ) (Rewriting.emb ψ))
  simpa only [encodeList_cons_natCast, Encodable.encode_list_nil, Nat.cast_zero,
    ← LogicalConnective.HomClass.map_imply, ← LogicalConnective.HomClass.map_neg,
    Semiformula.encode_emb, negateCode_encode_natCast] using h

def ProgramTheoryProvable (φ : M) : Prop :=
  ∃ p, generatedTheoryProofCheck.evalArithmetic (Arithmetic.pair φ p) = 1

theorem programTheoryProvable_iff (φ : M) :
    ProgramTheoryProvable φ ↔ (formulaCheck false).evalArithmetic (Arithmetic.pair 0 φ) = 1 ∧
      ∃ rows, generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair 0 rows) = 1 ∧
        ProgramLKProvable (generatedTheorySequent.evalArithmetic (Arithmetic.pair φ rows)) := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨rows, cert, rfl⟩ := arithmeticPair_cases p
    obtain ⟨hf, ha, hc⟩ := (evalArithmetic_generatedTheoryProofCheck φ rows cert).mp hp
    exact ⟨hf, rows, ha, cert, hc⟩
  · rintro ⟨hf, rows, ha, cert, hc⟩
    exact ⟨Arithmetic.pair rows cert,
      (evalArithmetic_generatedTheoryProofCheck φ rows cert).mpr ⟨hf, ha, hc⟩⟩

theorem ProgramTheoryProvable.modusPonens (φ ψ : SetTheorySentence)
    (himp : ProgramTheoryProvable (Encodable.encode (φ 🡒 ψ) : M))
    (hφ : ProgramTheoryProvable (Encodable.encode φ : M)) :
    ProgramTheoryProvable (Encodable.encode ψ : M) := by
  obtain ⟨_, rows₁, ha₁, hp₁⟩ := (programTheoryProvable_iff _).mp himp
  obtain ⟨_, rows₂, ha₂, hp₂⟩ := (programTheoryProvable_iff _).mp hφ
  apply (programTheoryProvable_iff _).mpr
  refine ⟨formulaCheck_encode_natCast false Empty.elim ψ,
    listAppend.evalArithmetic (Arithmetic.pair rows₂ rows₁),
    (evalArithmetic_generatedAxiomRowsCheck_append _ _).mpr ⟨ha₁, ha₂⟩, ?_⟩
  rw [evalArithmetic_generatedTheorySequent] at hp₁ hp₂ ⊢
  rw [evalArithmetic_listMap_append]
  exact ProgramLKProvable.contextual_modusPonens
    (programLKProvable_modusPonens_sequent φ ψ) hp₁ hp₂

end PrimitiveProgram
end ZFVP
