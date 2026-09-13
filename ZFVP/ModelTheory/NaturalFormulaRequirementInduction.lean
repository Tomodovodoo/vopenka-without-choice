import ZFVP.ModelTheory.InternalFormulaRequirements

/-! Constructor induction for every internally accepted natural formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalFormulaRequirement_induction (allowFree : Bool) (P : V → V → Prop)
    (hP : ℒₛₑₜ-relation P)
    (hrel : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) →
      requirementFits ((atomicRequirement allowFree).evalSet a) n →
      P n (SetTheory.succ (naturalSquarePair 0 a)))
    (hnrel : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) →
      requirementFits ((atomicRequirement allowFree).evalSet a) n →
      P n (SetTheory.succ (naturalSquarePair 1 a)))
    (htrue : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) → P n (SetTheory.succ (naturalSquarePair 2 a)))
    (hfalse : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) → P n (SetTheory.succ (naturalSquarePair 3 a)))
    (hand : ∀ n a b, n ∈ (ω : V) → a ∈ (ω : V) → b ∈ (ω : V) →
      requirementFits ((formulaRequirement allowFree).evalSet a) n →
      requirementFits ((formulaRequirement allowFree).evalSet b) n → P n a → P n b →
      P n (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair a b))))
    (hor : ∀ n a b, n ∈ (ω : V) → a ∈ (ω : V) → b ∈ (ω : V) →
      requirementFits ((formulaRequirement allowFree).evalSet a) n →
      requirementFits ((formulaRequirement allowFree).evalSet b) n → P n a → P n b →
      P n (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair a b))))
    (hall : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) →
      requirementFits ((formulaRequirement allowFree).evalSet a) (SetTheory.succ n) →
      P (SetTheory.succ n) a → P n (SetTheory.succ (naturalSquarePair 6 a)))
    (hexis : ∀ n a, n ∈ (ω : V) → a ∈ (ω : V) →
      requirementFits ((formulaRequirement allowFree).evalSet a) (SetTheory.succ n) →
      P (SetTheory.succ n) a → P n (SetTheory.succ (naturalSquarePair 7 a)))
    {c n : V} (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) : P n c := by
  classical
  have H : ∀ c : Ordinal V, (c : V) ∈ (ω : V) → ∀ n ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet (c : V)) n → P n c := by
    apply transfinite_induction (P := fun c : V ↦ c ∈ (ω : V) → ∀ n ∈ (ω : V),
      requirementFits ((formulaRequirement allowFree).evalSet c) n → P n c) (by definability)
    intro c ih hc n hn hv
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
    have hp : naturalSquarePair (naturalSquareLeft a) (naturalSquareRight a) = a :=
      (naturalSquareUnpair_spec ha).2.2
    have hrec {d : V} (hd : d ∈ (c : V)) (hdω : d ∈ (ω : V)) : ∀ m ∈ (ω : V),
        requirementFits ((formulaRequirement allowFree).evalSet d) m → P m d := by
      have : IsOrdinal d := IsOrdinal.of_mem hdω
      exact ih (IsOrdinal.toOrdinal d) hd hdω
    rw [he, evalSet_formulaRequirement_tagged allowFree ht ha] at hv
    rw [he]
    unfold naturalFormulaRequirementValue at hv
    split_ifs at hv with h0 h1 h2 h3 h4 h5 h6 h7
    · simpa only [h0] using hrel n a hn ha hv
    · simpa only [h1] using hnrel n a hn ha hv
    · simpa only [h2] using htrue n a hn ha
    · simpa only [h3] using hfalse n a hn ha
    · obtain ⟨hl, hr⟩ := (requirementFits_join
        (evalSet_natural _ (naturalSquareLeft_natural a))
        (evalSet_natural _ (naturalSquareRight_natural a)) hn).mp hv
      simpa only [hp, h4] using hand n (naturalSquareLeft a) (naturalSquareRight a) hn
        (naturalSquareLeft_natural a) (naturalSquareRight_natural a) hl hr
        (hrec hlmem (naturalSquareLeft_natural a) n hn hl)
        (hrec hrmem (naturalSquareRight_natural a) n hn hr)
    · obtain ⟨hl, hr⟩ := (requirementFits_join
        (evalSet_natural _ (naturalSquareLeft_natural a))
        (evalSet_natural _ (naturalSquareRight_natural a)) hn).mp hv
      simpa only [hp, h5] using hor n (naturalSquareLeft a) (naturalSquareRight a) hn
        (naturalSquareLeft_natural a) (naturalSquareRight_natural a) hl hr
        (hrec hlmem (naturalSquareLeft_natural a) n hn hl)
        (hrec hrmem (naturalSquareRight_natural a) n hn hr)
    · have hb := (requirementFits_quantify (evalSet_natural _ ha) hn).mp hv
      simpa only [h6] using hall n a hn ha hb (hrec hmem ha (SetTheory.succ n) (ω_succ_closed hn) hb)
    · have hb := (requirementFits_quantify (evalSet_natural _ ha) hn).mp hv
      simpa only [h7] using hexis n a hn ha hb (hrec hmem ha (SetTheory.succ n) (ω_succ_closed hn) hb)
    · exact False.elim (hv.1 rfl)
  have : IsOrdinal c := IsOrdinal.of_mem hc
  exact H (IsOrdinal.toOrdinal c) hc n hn hv

end ZFVP