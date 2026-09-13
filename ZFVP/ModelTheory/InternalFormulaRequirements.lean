import ZFVP.ModelTheory.InternalFormulaRequirementEquations

/-! Soundness of formula requirement checks on every internal natural input. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalCode_cases {c : V} (hc : c ∈ (ω : V)) :
    c = 0 ∨ ∃ t ∈ (ω : V), ∃ a ∈ (ω : V), c = SetTheory.succ (naturalSquarePair t a) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  rcases listCode_cases u with hu | ⟨t, a, hu⟩
  · exact Or.inl (by rw [hu, internalArithmeticVal_zero])
  · refine Or.inr ⟨internalArithmeticVal t, internalArithmeticVal_mem t,
      internalArithmeticVal a, internalArithmeticVal_mem a, ?_⟩
    rw [hu, internalArithmeticVal_succ, internalArithmeticVal_pair]

theorem naturalCode_payload_mem {t a : V} (ht : t ∈ (ω : V)) (ha : a ∈ (ω : V)) :
    a ∈ SetTheory.succ (naturalSquarePair t a) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ht
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective ha
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ, ← internalArithmetic_lt]
  exact lt_succ_iff_le.mpr (le_pair_right u v)

theorem decodedNaturalAtomic_payload_valid (allowFree : Bool) {c n : V}
    (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet c) n) :
    IsAtomicArguments membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n
      (relationToken (naturalSquareLeft (naturalSquareRight c)))
      (decodedNaturalArguments (naturalSquareRight (naturalSquareRight c))) := by
  have he : naturalSquarePair (naturalSquareLeft c) (naturalSquareRight c) = c :=
    (naturalSquareUnpair_spec hc).2.2
  have he2 : naturalSquarePair (naturalSquareLeft (naturalSquareRight c))
      (naturalSquareRight (naturalSquareRight c)) = naturalSquareRight c :=
    (naturalSquareUnpair_spec (naturalSquareRight_natural c)).2.2
  apply decodedNaturalAtomic_valid allowFree (naturalSquareLeft_natural c)
    (naturalSquareLeft_natural _) (naturalSquareRight_natural _) hn
  simpa only [he2, he] using hv

theorem decodedNaturalFormula_valid (allowFree : Bool) {c n : V}
    (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) :
    decodedNaturalFormula c ∈ formulaSet membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n := by
  classical
  have H : ∀ c : Ordinal V, (c : V) ∈ (ω : V) → ∀ n ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet (c : V)) n →
        ⟨n, decodedNaturalFormula (c : V)⟩ₖ ∈ formulaFamily (V := V) membershipLanguageCode (naturalSyntaxFreeDomain allowFree) := by
    apply transfinite_induction (P := fun c : V ↦ c ∈ (ω : V) → ∀ n ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) n →
        ⟨n, decodedNaturalFormula c⟩ₖ ∈ formulaFamily (V := V) membershipLanguageCode (naturalSyntaxFreeDomain allowFree))
      (by definability)
    intro c ih hc n hn hv
    have Hclosed := formulaFamily_closed (membershipLanguageCode_valid (V := V))
      (naturalSyntaxFreeDomain allowFree) n hn
    rcases naturalCode_cases hc with hzero | ⟨t, ht, a, ha, he⟩
    · simp [hzero, evalSet_formulaRequirement_zero, requirementFits] at hv
    have hmem : a ∈ (c : V) := he ▸ naturalCode_payload_mem ht ha
    have : IsOrdinal a := IsOrdinal.of_mem ha
    have hsubmem {d : V} (hdω : d ∈ (ω : V)) (hs : d ⊆ a) : d ∈ (c : V) := by
      have : IsOrdinal d := IsOrdinal.of_mem hdω
      rcases IsOrdinal.subset_iff.mp hs with heq | hd
      · rw [heq]
        exact hmem
      · exact IsTransitive.transitive _ hmem _ hd
    have hlmem := hsubmem (naturalSquareLeft_natural a) (naturalSquareLeft_subset ha)
    have hrmem := hsubmem (naturalSquareRight_natural a) (naturalSquareRight_subset ha)
    have hrec {d : V} (hd : d ∈ (c : V)) (hdω : d ∈ (ω : V)) : ∀ m ∈ (ω : V),
        requirementFits ((formulaRequirement allowFree).evalSet d) m →
          ⟨m, decodedNaturalFormula d⟩ₖ ∈ formulaFamily (V := V) membershipLanguageCode (naturalSyntaxFreeDomain allowFree) := by
      have : IsOrdinal d := IsOrdinal.of_mem hdω
      exact ih (IsOrdinal.toOrdinal d) hd hdω
    rw [he, evalSet_formulaRequirement_tagged allowFree ht ha] at hv
    rw [he, decodedNaturalFormula_tagged ht ha]
    unfold naturalFormulaRequirementValue at hv
    split_ifs at hv with h0 h1 h2 h3 h4 h5 h6 h7
    · simpa only [naturalFormulaDecodeValue, h0, ite_true] using
        (Hclosed.2.1 _ _ (decodedNaturalAtomic_payload_valid allowFree ha hn hv)).1
    · simpa [naturalFormulaDecodeValue, h1, OfNat.ofNat, setNumeral_eq_iff] using
        (Hclosed.2.1 _ _ (decodedNaturalAtomic_payload_valid allowFree ha hn hv)).2
    · simpa [naturalFormulaDecodeValue, h2, OfNat.ofNat, setNumeral_eq_iff] using Hclosed.1.1
    · simpa [naturalFormulaDecodeValue, h3, OfNat.ofNat, setNumeral_eq_iff] using Hclosed.1.2
    · obtain ⟨hl, hr⟩ := (requirementFits_join
        (evalSet_natural _ (naturalSquareLeft_natural a))
        (evalSet_natural _ (naturalSquareRight_natural a)) hn).mp hv
      have hleft := hrec hlmem (naturalSquareLeft_natural a) n hn hl
      have hright := hrec hrmem (naturalSquareRight_natural a) n hn hr
      simpa [naturalFormulaDecodeValue, h4, OfNat.ofNat, setNumeral_eq_iff] using
        (Hclosed.2.2.1 _ _ hleft hright).1
    · obtain ⟨hl, hr⟩ := (requirementFits_join
        (evalSet_natural _ (naturalSquareLeft_natural a))
        (evalSet_natural _ (naturalSquareRight_natural a)) hn).mp hv
      have hleft := hrec hlmem (naturalSquareLeft_natural a) n hn hl
      have hright := hrec hrmem (naturalSquareRight_natural a) n hn hr
      simpa [naturalFormulaDecodeValue, h5, OfNat.ofNat, setNumeral_eq_iff] using
        (Hclosed.2.2.1 _ _ hleft hright).2
    · have hbody := hrec hmem ha (SetTheory.succ n) (ω_succ_closed hn)
        ((requirementFits_quantify (evalSet_natural _ ha) hn).mp hv)
      simpa [naturalFormulaDecodeValue, h6, OfNat.ofNat, setNumeral_eq_iff] using
        (Hclosed.2.2.2 _ hbody).1
    · have hbody := hrec hmem ha (SetTheory.succ n) (ω_succ_closed hn)
        ((requirementFits_quantify (evalSet_natural _ ha) hn).mp hv)
      simpa [naturalFormulaDecodeValue, h7, OfNat.ofNat, setNumeral_eq_iff] using
        (Hclosed.2.2.2 _ hbody).2
    · exact False.elim (hv.1 rfl)
  have : IsOrdinal c := IsOrdinal.of_mem hc
  exact (mem_formulaSet_iff _ _ _ _).mpr (H (IsOrdinal.toOrdinal c) hc n hn hv)

end ZFVP