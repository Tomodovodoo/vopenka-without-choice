import ZFVP.ModelTheory.InternalLKCertificateEquations

/-! Soundness of the explicit LK certificate checker, including nonstandard finite certificates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_lkCertificateRun_sound {M z p : V}
    (hM : IsStructureCode membershipLanguageCode M) (hz : z ∈ (ω : V)) (hp : p ∈ (ω : V))
    (hcheck : naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)) = 1) :
    ∀ C ∈ range (decodedNaturalList
      (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)))),
      NaturalSequentValid M C := by
  have H : ∀ p ∈ (ω : V),
      naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)) = 1 →
      ∀ C ∈ range (decodedNaturalList
        (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)))),
        NaturalSequentValid M C := by
    intro p hp
    apply naturalListCode_induction (fun p ↦
      naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)) = 1 →
      ∀ C ∈ range (decodedNaturalList
        (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)))),
        NaturalSequentValid M C) (by definability) ?_ ?_ hp
    · intro _ C hC
      rw [evalSet_lkCertificateRun_zero hz] at hC
      have hzero : naturalSquareLeft (naturalSquarePair (0 : V) 1) = 0 :=
        congrArg Prod.fst (naturalSquareUnpair_pair (by simp [zero_def]) (by simp))
      simp only [hzero, range_decodedNaturalList_zero] at hC
      exact False.elim (SetTheory.not_mem_empty hC)
    · intro row p hrow hp ih hacc C hC
      obtain ⟨D, hD, w, hw, rfl⟩ := naturalSquarePair_surjective hrow
      obtain ⟨hprev, hrule⟩ := (evalSet_lkCertificateRun_cons_right_eq_one hz hD hw hp).mp hacc
      rw [evalSet_lkCertificateRun_cons_left hz hD hw hp,
        mem_range_decodedNaturalList_cons hD (naturalSquareLeft_natural _)] at hC
      rcases hC with rfl | hC
      · exact evalSet_lkRuleCheck_sound_raw hM (naturalSquareLeft_natural _) hD hw hrule (ih hprev)
      · exact ih hprev C hC
  exact H p hp hcheck

theorem evalSet_lkProofCheck_sound {M C p : V}
    (hM : IsStructureCode membershipLanguageCode M) (hC : C ∈ (ω : V)) (hp : p ∈ (ω : V))
    (hcheck : lkProofCheck.evalSet (naturalSquarePair C p) = 1) : NaturalSequentValid M C := by
  obtain ⟨hacc, hmem⟩ := (evalSet_lkProofCheck_eq_one hC hp).mp hcheck
  exact evalSet_lkCertificateRun_sound hM (by simp [zero_def]) hp hacc C hmem

end ZFVP
