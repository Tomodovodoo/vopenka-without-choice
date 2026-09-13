import ZFVP.ModelTheory.InternalSyntaxChecks
import ZFVP.ModelTheory.InternalProofRewriteSemantics
import ZFVP.Syntax.PrimitiveProgramSequentOperations

/-! Satisfaction of natural-number sequent codes under internal omega-indexed assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def NaturalSequentHolds (M e cs : V) : Prop :=
  ∃ c ∈ range (decodedNaturalList cs), Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula c) ∅

instance naturalSequentHolds_definable : ℒₛₑₜ-relation₃[V] NaturalSequentHolds := by
  unfold NaturalSequentHolds Satisfies
  definability

def NaturalSequentValid (M cs : V) : Prop :=
  ∀ e ∈ structureDomain M ^ (ω : V), NaturalSequentHolds M e cs

instance naturalSequentValid_definable : ℒₛₑₜ-relation[V] NaturalSequentValid := by
  unfold NaturalSequentValid
  definability

@[simp] theorem naturalSequentHolds_zero (M e : V) : ¬ NaturalSequentHolds M e 0 := by
  simp [NaturalSequentHolds]

theorem naturalSequentHolds_cons (M e : V) {c cs : V} (hc : c ∈ (ω : V)) (hcs : cs ∈ (ω : V)) :
    NaturalSequentHolds M e (succ (naturalSquarePair c cs)) ↔
      Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula c) ∅ ∨ NaturalSequentHolds M e cs := by
  simp only [NaturalSequentHolds, mem_range_decodedNaturalList_cons hc hcs, exists_eq_or_imp]

theorem naturalSequentHolds_append (M e : V) {xs ys : V} (hxs : xs ∈ (ω : V)) (hys : ys ∈ (ω : V)) :
    NaturalSequentHolds M e (listAppend.evalSet (naturalSquarePair ys xs)) ↔
      NaturalSequentHolds M e xs ∨ NaturalSequentHolds M e ys := by
  simp only [NaturalSequentHolds, mem_range_decodedNaturalList_append hxs hys, or_and_right, exists_or]

theorem NaturalSequentHolds.mono {M e xs ys : V}
    (h : NaturalSequentHolds M e xs) (hsub : range (decodedNaturalList xs) ⊆ range (decodedNaturalList ys)) :
    NaturalSequentHolds M e ys := by
  obtain ⟨c, hc, hv⟩ := h
  exact ⟨c, hsub c hc, hv⟩

theorem NaturalSequentValid.mono {M xs ys : V}
    (h : NaturalSequentValid M xs) (hsub : range (decodedNaturalList xs) ⊆ range (decodedNaturalList ys)) :
    NaturalSequentValid M ys := fun e he ↦ (h e he).mono hsub

theorem evalSet_proofRewriteAtZero {s c : V} (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    proofRewriteAtZero.evalSet (naturalSquarePair s c) = proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c)) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteAtZero u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem mem_range_proofRewriteSequent {s cs : V} (hs : s ∈ (ω : V)) (hcs : cs ∈ (ω : V)) (x : V) :
    x ∈ range (decodedNaturalList (proofRewriteSequent.evalSet (naturalSquarePair s cs))) ↔
      ∃ c ∈ range (decodedNaturalList cs), x = proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c)) := by
  rw [proofRewriteSequent, mem_range_decodedNaturalList_map proofRewriteAtZero hs hcs]
  exact exists_congr (fun c ↦ and_congr_right (fun hc ↦ by
    rw [evalSet_proofRewriteAtZero hs (mem_decodedNaturalList_range_natural hcs hc)]))

theorem naturalSequentHolds_shift_prepend {M e cs x : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hx : x ∈ structureDomain M) (hcs : cs ∈ (ω : V))
    (hv : naturalSequentFits true 0 cs) :
    NaturalSequentHolds M (omegaAssignmentPrepend e x) (proofRewriteSequent.evalSet (naturalSquarePair 0 cs)) ↔
      NaturalSequentHolds M e cs := by
  unfold NaturalSequentHolds
  constructor
  · rintro ⟨c, hc, hsat⟩
    obtain ⟨a, ha, rfl⟩ := (mem_range_proofRewriteSequent (by simp [zero_def]) hcs c).mp hc
    exact ⟨a, ha, (satisfies_proofRewrite_shift_prepend hM he hx
      (mem_decodedNaturalList_range_natural hcs ha) (hv a ha)).mp hsat⟩
  · rintro ⟨a, ha, hsat⟩
    refine ⟨_, (mem_range_proofRewriteSequent (by simp [zero_def]) hcs _).mpr ⟨a, ha, rfl⟩, ?_⟩
    exact (satisfies_proofRewrite_shift_prepend hM he hx
      (mem_decodedNaturalList_range_natural hcs ha) (hv a ha)).mpr hsat

end ZFVP
