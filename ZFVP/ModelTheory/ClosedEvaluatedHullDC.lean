import ZFVP.ModelTheory.ShortSequenceWitnessTables
import ZFVP.ModelTheory.ShortEvaluatedRepresentatives
import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.SetTheory.WellOrderedDependentChoice

/-! Dense next-step witnesses in a well-orderable evaluated set give DC at
an arbitrary checked ordinal. Short sequences are lifted to ground names. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem dependentChoicePath_of_dense_short_name_witnesses (M : ForcingContext V)
    {κ C p : V} [IsOrdinal κ] (AN RN : ForcingName M.P)
    (hC : ∀ σ ∈ C, IsForcingName M.P σ)
    (hw : IsWellOrderable (M.check C)) (hp : p ∈ M.G)
    (hrep : ∀ η ∈ κ, ∀ s : M.Model,
      s ∈ range (M.evaluationGraph C hC) ^ M.check η →
      ∃ t, ∃ htN : IsNameSequence M.P t, t ∈ C ^ η ∧ M.sequenceValue t htN = s)
    (hstep : ∀ t ∈ shorterSequences κ C, ∀ q ∈ M.P, ⟨q, p⟩ₖ ∈ M.R →
      q ∈ forcingFormula M.P M.R shortSequenceInputFormula
        (standardTuple ![checkName M.one κ, AN.val, sequenceName M.one t]) →
      ∃ r ∈ M.P, ∃ σ ∈ C, ⟨r, q⟩ₖ ∈ M.R ∧
        r ∈ forcingFormula M.P M.R dependentChoiceNextFormula
          (standardTuple ![sequenceName M.one t, σ, AN.val, RN.val])) :
    ∃ f, IsDependentChoicePath (M.ofName AN) (M.ofName RN) (M.check κ) f := by
  let H := range (M.evaluationGraph C hC)
  let B := M.ofName AN ∩ H
  have hBH : B ⊆ H := fun _ hz ↦ (mem_inter_iff.mp hz).2
  have hBA : B ⊆ M.ofName AN := fun _ hz ↦ (mem_inter_iff.mp hz).1
  have hwoH : IsWellOrderable H := wellOrderable_of_surjective_function hw
    (M.evaluationGraph_mem_function C hC) rfl
  have hwoB : IsWellOrderable B := by
    obtain ⟨ξ, hξ, hi⟩ := (wellOrderable_iff_cardLE_ordinal H).mp hwoH
    exact (wellOrderable_iff_cardLE_ordinal B).mpr ⟨ξ, hξ, (cardLE_of_subset hBH).trans hi⟩
  have hserial : ∀ s ∈ shorterSequences (M.check κ) B, ∃ y ∈ B, ⟨s, y⟩ₖ ∈ M.ofName RN := by
    intro s hs
    obtain ⟨η', hη', hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    obtain ⟨η, hη, rfl⟩ := (M.mem_check_iff κ η').mp hη'
    let := IsOrdinal.of_mem hη
    obtain ⟨t, htN, ht, hts⟩ := hrep η hη s (mem_function_of_mem_function_of_subset hsf hBH)
    have htt : t ∈ shorterSequences κ C := (mem_shorterSequences _ _ _).mpr ⟨η, hη, ht⟩
    let KN : ForcingName M.P := ⟨checkName M.one κ, checkName_isName M.top.1 κ⟩
    let TN : ForcingName M.P := ⟨sequenceName M.one t, sequenceName_isName M.top.1 htN⟩
    have hshort : M.ofName TN ∈ shorterSequences (M.check κ) (M.ofName AN) := by
      rw [show M.ofName TN = s from hts]
      exact (mem_shorterSequences _ _ _).mpr ⟨M.check η, (M.check_mem_iff _ _).mpr hη,
        mem_function_of_mem_function_of_subset hsf hBA⟩
    have hinput := (eval_shortSequenceInputFormula (fun i ↦ M.ofName (![KN, AN, TN] i))).mpr hshort
    obtain ⟨q, hqG, hqf⟩ := (M.formula_truth shortSequenceInputFormula ![KN, AN, TN]).mp hinput
    obtain ⟨u, huG, hup, huq⟩ := M.generic.1.2.2.2 p hp q hqG
    have huP := M.generic.1.1 u huG
    have huf := (forcingFormula_regular M.order shortSequenceInputFormula _).2.1 q hqf u huP huq
    let D := {r ∈ M.P ; ∃ σ ∈ C,
      r ∈ forcingFormula M.P M.R dependentChoiceNextFormula
        (standardTuple ![sequenceName M.one t, σ, AN.val, RN.val])}
    have hD : ForcingDenseBelow M.P M.R D u := by
      refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
      intro v hv hvu
      have hvp := M.order.2.2 v hv u huP p (M.generic.1.1 p hp) hvu hup
      have hvf := (forcingFormula_regular M.order shortSequenceInputFormula _).2.1 u huf v hv hvu
      obtain ⟨r, hr, σ, hσ, hrv, hrf⟩ := hstep t htt v hv hvp hvf
      exact ⟨r, mem_sep_iff.mpr ⟨hr, σ, hσ, hrf⟩, hrv⟩
    obtain ⟨r, hrG, hrD⟩ := externalForcingGeneric_meets_denseBelow M.order M.generic huG hD
    obtain ⟨σ, hσ, hrf⟩ := (mem_sep_iff.mp hrD).2
    let SN : ForcingName M.P := ⟨σ, hC σ hσ⟩
    have hnext := (eval_dependentChoiceNextFormula _).mp
      ((M.formula_truth dependentChoiceNextFormula ![TN, SN, AN, RN]).mpr ⟨r, hrG, hrf⟩)
    refine ⟨M.ofName SN, mem_inter_iff.mpr ⟨hnext.1,
      (M.mem_range_evaluationGraph_iff C hC _).mpr ⟨σ, hσ, rfl⟩⟩, ?_⟩
    have hn : ⟨M.ofName TN, M.ofName SN⟩ₖ ∈ M.ofName RN := by simpa using hnext.2
    simpa only [show M.ofName TN = s from hts] using hn
  obtain ⟨f, hf⟩ := dependentChoicePath_of_wellOrderable hwoB hserial
  exact ⟨f, mem_function_of_mem_function_of_subset hf.1 hBA, hf.2⟩

end ForcingContext
end ZFVP
