import ZFVP.ModelTheory.CountableEvaluatedHull
import ZFVP.ModelTheory.SerialForcingCandidates

/-! Dense forcing witnesses among a checked countable set of names yield
an internal path through the interpreted serial relation. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem serialPath_of_dense_name_witnesses (M : ForcingContext V)
    (A S : ForcingName M.P) {C p : V}
    (hC : ∀ ν ∈ C, IsForcingName M.P ν)
    (hc : IsInternallyCountable (M.check C)) (hp : p ∈ M.G)
    (hi : ∀ q ∈ M.P, ⟨q, p⟩ₖ ∈ M.R → ∃ r ∈ M.P, ∃ ν ∈ C,
      ⟨r, q⟩ₖ ∈ M.R ∧ r ∈ forcingFormula M.P M.R serialHullInitialFormula
        (standardTuple ![A.val, ν]))
    (hs : ∀ τ ∈ C, ∀ q ∈ M.P, ⟨q, p⟩ₖ ∈ M.R →
      q ∈ forcingFormula M.P M.R serialHullInitialFormula (standardTuple ![A.val, τ]) →
      ∃ r ∈ M.P, ∃ ν ∈ C, ⟨r, q⟩ₖ ∈ M.R ∧
        r ∈ forcingFormula M.P M.R serialHullNextFormula (standardTuple ![A.val, S.val, τ, ν])) :
    ∃ f ∈ (M.ofName A) ^ (ω : M.Model),
      ∀ n ∈ (ω : M.Model), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ M.ofName S := by
  let H := range (M.evaluationGraph C hC)
  have hH : IsInternallyCountable H := M.internallyCountable_evaluation_range hc
    (fun _ h ↦ h) hC
  let D := {r ∈ M.P ; ∃ ν ∈ C,
    r ∈ forcingFormula M.P M.R serialHullInitialFormula (standardTuple ![A.val, ν])}
  have hd : ForcingDenseBelow M.P M.R D p := by
    refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
    intro q hq hqp
    obtain ⟨r, hr, ν, hν, hrq, hf⟩ := hi q hq hqp
    exact ⟨r, mem_sep_iff.mpr ⟨hr, ν, hν, hf⟩, hrq⟩
  obtain ⟨r, hrG, hrD⟩ := externalForcingGeneric_meets_denseBelow M.order M.generic hp hd
  obtain ⟨ν, hν, hf⟩ := (mem_sep_iff.mp hrD).2
  let νN : ForcingName M.P := ⟨ν, hC ν hν⟩
  have hνA : M.ofName νN ∈ M.ofName A := (eval_serialHullInitialFormula _).mp
    ((M.formula_truth serialHullInitialFormula ![A, νN]).mpr ⟨r, hrG, hf⟩)
  have hνH : M.ofName νN ∈ H := (M.mem_range_evaluationGraph_iff C hC _).mpr ⟨ν, hν, rfl⟩
  apply dependentChoice_of_wellOrderable_serial_subset
    (B := M.ofName A ∩ H) (fun _ h ↦ (mem_inter_iff.mp h).1)
    ((internallyCountable_subset hH (fun _ h ↦ (mem_inter_iff.mp h).2)).wellOrderable)
    ⟨M.ofName νN, mem_inter_iff.mpr ⟨hνA, hνH⟩⟩
  intro x hx
  obtain ⟨hxA, hxH⟩ := mem_inter_iff.mp hx
  obtain ⟨τ, hτ, rfl⟩ := (M.mem_range_evaluationGraph_iff C hC x).mp hxH
  let τN : ForcingName M.P := ⟨τ, hC τ hτ⟩
  have he : serialHullInitialFormula.Evalb (fun i ↦ M.ofName (![A, τN] i)) :=
    (eval_serialHullInitialFormula _).mpr hxA
  obtain ⟨q, hqG, hqf⟩ := (M.formula_truth serialHullInitialFormula ![A, τN]).mp he
  obtain ⟨t, htG, htp, htq⟩ := M.generic.1.2.2.2 p hp q hqG
  have htP := M.generic.1.1 t htG
  have htf := (forcingFormula_regular M.order serialHullInitialFormula _).2.1 q hqf t htP htq
  let E := {r ∈ M.P ; ∃ ν ∈ C,
    r ∈ forcingFormula M.P M.R serialHullNextFormula (standardTuple ![A.val, S.val, τ, ν])}
  have hed : ForcingDenseBelow M.P M.R E t := by
    refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
    intro u hu hut
    have hup := M.order.2.2 u hu t htP p (M.generic.1.1 p hp) hut htp
    have huf := (forcingFormula_regular M.order serialHullInitialFormula _).2.1 t htf u hu hut
    obtain ⟨r, hr, ν, hν, hru, hf⟩ := hs τ hτ u hu hup huf
    exact ⟨r, mem_sep_iff.mpr ⟨hr, ν, hν, hf⟩, hru⟩
  obtain ⟨r, hrG, hrE⟩ := externalForcingGeneric_meets_denseBelow M.order M.generic htG hed
  obtain ⟨ν, hν, hf⟩ := (mem_sep_iff.mp hrE).2
  let υN : ForcingName M.P := ⟨ν, hC ν hν⟩
  have hv := (eval_serialHullNextFormula _).mp
    ((M.formula_truth serialHullNextFormula ![A, S, τN, υN]).mpr ⟨r, hrG, hf⟩)
  exact ⟨M.ofName υN, mem_inter_iff.mpr ⟨hv.1,
    (M.mem_range_evaluationGraph_iff C hC _).mpr ⟨ν, hν, rfl⟩⟩, hv.2⟩

end ForcingContext
end ZFVP
