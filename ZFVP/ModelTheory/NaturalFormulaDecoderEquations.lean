import ZFVP.ModelTheory.NaturalFormulaDecoder

/-! Constructor equations for the natural-number formula decoder at every internal input. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem setNumeral_eq_iff (m n : ℕ) : (SetTheory.ofNat m : V) = SetTheory.ofNat n ↔ m = n :=
  natCast_eq_iff m n

noncomputable def naturalFormulaDecodeValue (t c : V) (F : V → V) : V := by
  classical
  let r := relationToken (naturalSquareLeft (naturalSquareRight c))
  let a := decodedNaturalArguments (naturalSquareRight (naturalSquareRight c))
  exact if t = 0 then atomCode r a else
    if t = 1 then negAtomCode r a else
    if t = 2 then truthCode else
    if t = 3 then falsityCode else
    if t = 4 then andCode (F (naturalSquareLeft c)) (F (naturalSquareRight c)) else
    if t = 5 then orCode (F (naturalSquareLeft c)) (F (naturalSquareRight c)) else
    if t = 6 then allCode (F c) else
    if t = 7 then existsCode (F c) else ∅

theorem naturalSquarePair_right_subset {t c : V} (ht : t ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    c ⊆ naturalSquarePair t c := by
  have h := naturalSquareRight_subset (naturalSquarePair_natural ht hc)
  simpa only [naturalSquareRight, naturalSquareUnpair_pair ht hc] using h

theorem decodedNaturalFormula_tagged {t c : V} (ht : t ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair t c)) =
      naturalFormulaDecodeValue t c decodedNaturalFormula := by
  classical
  have hp := naturalSquarePair_natural ht hc
  have : IsOrdinal c := IsOrdinal.of_mem hc
  have : IsOrdinal (naturalSquarePair t c) := IsOrdinal.of_mem hp
  have : IsOrdinal (naturalSquareLeft c) := IsOrdinal.of_mem (naturalSquareLeft_natural c)
  have : IsOrdinal (naturalSquareRight c) := IsOrdinal.of_mem (naturalSquareRight_natural c)
  have hcp := naturalSquarePair_right_subset ht hc
  have hcN := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hcp)
  have hlN := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_trans (naturalSquareLeft_subset hc) hcp))
  have hrN := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_trans (naturalSquareRight_subset hc) hcp))
  rw [decodedNaturalFormula_unfold (ω_succ_closed hp)]
  unfold naturalFormulaDecodeStep
  dsimp only
  simp only [domain_definableGraph]
  rw [evalSet_listHead_cons ht hc]
  simp [naturalCons_ne_zero,
    evalSet_listTail_cons ht hc, naturalFormulaDecodeValue,
    value_definableGraph _ _ _ hcN, value_definableGraph _ _ _ hlN, value_definableGraph _ _ _ hrN]

@[simp] theorem decodedNaturalFormula_zero : decodedNaturalFormula (0 : V) = ∅ := by
  rw [decodedNaturalFormula_unfold (by simp [zero_def])]
  simp [naturalFormulaDecodeStep, domain_definableGraph]

@[simp] theorem decodedNaturalFormula_rel {c : V} (hc : c ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 0 c)) =
      atomCode (relationToken (naturalSquareLeft (naturalSquareRight c)))
        (decodedNaturalArguments (naturalSquareRight (naturalSquareRight c))) := by
  rw [decodedNaturalFormula_tagged (by simp [zero_def]) hc]
  simp [naturalFormulaDecodeValue]

@[simp] theorem decodedNaturalFormula_nrel {c : V} (hc : c ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 1 c)) =
      negAtomCode (relationToken (naturalSquareLeft (naturalSquareRight c)))
        (decodedNaturalArguments (naturalSquareRight (naturalSquareRight c))) := by
  rw [decodedNaturalFormula_tagged (show (1 : V) ∈ (ω : V) from ofNat_mem_ω 1) hc]
  simp [naturalFormulaDecodeValue]

@[simp] theorem decodedNaturalFormula_verum {c : V} (hc : c ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 2 c)) = truthCode := by
  rw [decodedNaturalFormula_tagged (show (2 : V) ∈ (ω : V) from ofNat_mem_ω 2) hc]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff]

@[simp] theorem decodedNaturalFormula_falsum {c : V} (hc : c ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 3 c)) = falsityCode := by
  rw [decodedNaturalFormula_tagged (show (3 : V) ∈ (ω : V) from ofNat_mem_ω 3) hc]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff]

@[simp] theorem decodedNaturalFormula_and {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair a b))) =
      andCode (decodedNaturalFormula a) (decodedNaturalFormula b) := by
  rw [decodedNaturalFormula_tagged (show (4 : V) ∈ (ω : V) from ofNat_mem_ω 4)
    (naturalSquarePair_natural ha hb)]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff,
    naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair ha hb]

@[simp] theorem decodedNaturalFormula_or {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair a b))) =
      orCode (decodedNaturalFormula a) (decodedNaturalFormula b) := by
  rw [decodedNaturalFormula_tagged (show (5 : V) ∈ (ω : V) from ofNat_mem_ω 5)
    (naturalSquarePair_natural ha hb)]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff,
    naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair ha hb]

@[simp] theorem decodedNaturalFormula_all {a : V} (ha : a ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 6 a)) =
      allCode (decodedNaturalFormula a) := by
  rw [decodedNaturalFormula_tagged (show (6 : V) ∈ (ω : V) from ofNat_mem_ω 6) ha]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff]

@[simp] theorem decodedNaturalFormula_exs {a : V} (ha : a ∈ (ω : V)) :
    decodedNaturalFormula (SetTheory.succ (naturalSquarePair 7 a)) =
      existsCode (decodedNaturalFormula a) := by
  rw [decodedNaturalFormula_tagged (show (7 : V) ∈ (ω : V) from ofNat_mem_ω 7) ha]
  simp [naturalFormulaDecodeValue, OfNat.ofNat, setNumeral_eq_iff]
end ZFVP
