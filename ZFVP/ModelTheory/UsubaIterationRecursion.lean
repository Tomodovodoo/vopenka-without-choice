import ZFVP.ModelTheory.UsubaSaturatedIterand
import ZFVP.ModelTheory.WoodinIterationInitial
import ZFVP.SetTheory.ClassForcingTowerCodes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaInitialCode : V :=
  forcingInitialCode {∅} (reverseInclusionOrder {∅}) ∅

theorem usubaInitialCode_valid : IsForcingIterationCode (succ ∅) (usubaInitialCode : V) := by
  apply forcingInitialCode_valid (reverseInclusionOrder_poset _).1
  refine ⟨by simp, fun p hp ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr ?_⟩
  exact ⟨hp, by simp, empty_subset p⟩

noncomputable def usubaIterationSuccessor (k s : V) : V :=
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let Q := usubaSaturatedPosetName P R
  forcingSuccessorCode k s Q (reverseInclusionOrderName P R Q) ∅

instance usubaIterationSuccessor_definable : ℒₛₑₜ-function₂[V] usubaIterationSuccessor := by
  unfold usubaIterationSuccessor
  apply Language.DefinableFunction₅.comp (F := forcingSuccessorCode)
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₃.comp (F := reverseInclusionOrderName) <;> definability
  · definability

theorem usubaIterationSuccessor_valid {k s : V} [IsOrdinal k]
    (h : IsForcingIterationCode (succ k) s) :
    IsForcingIterationCode (succ (succ k)) (usubaIterationSuccessor k s) :=
  forcingSuccessorCode_valid h
    (usubaSaturated_iterand (h.system.order.preorder k (mem_succ_self k))
      (h.system.tops.top k (mem_succ_self k)))

theorem usubaIterationSuccessor_extends {k s : V}
    (h : IsForcingIterationCode (succ k) s) :
    ForcingCodeExtends s (usubaIterationSuccessor k s) :=
  forcingSuccessorCode_extends h _ _ _

noncomputable def usubaStageRule (θ s : V) : V := by
  classical
  exact if θ = ∅ then usubaInitialCode else if θ = succ (⋃ˢ θ) then
    usubaIterationSuccessor (⋃ˢ θ) s else forcingInverseCode θ s

instance usubaStageRule_definable : ℒₛₑₜ-function₂[V] usubaStageRule := by
  classical
  have h : ℒₛₑₜ-relation₃ (fun z θ s : V ↦
      (θ = ∅ ∧ z = usubaInitialCode) ∨
      (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧ z = usubaIterationSuccessor (⋃ˢ θ) s) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ z = forcingInverseCode θ s)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = usubaStageRule (v 1) (v 2) ↔ _
  unfold usubaStageRule
  split_ifs <;> tauto

theorem usubaStageRule_initial (s : V) : usubaStageRule ∅ s = usubaInitialCode := by
  simp [usubaStageRule]

theorem usubaStageRule_successor (k s : V) [IsOrdinal k] :
    usubaStageRule (succ k) s = usubaIterationSuccessor k s := by
  have hn : succ k ≠ (∅ : V) := by
    intro he
    exact not_mem_empty (he ▸ mem_succ_self k)
  simp [usubaStageRule, hn, sUnion_succ_of_transitive]

theorem usubaStageRule_valid {θ s : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) :
    IsForcingIterationCode (succ θ) (usubaStageRule θ s) := by
  classical
  by_cases hz : θ = ∅
  · subst θ
    simpa only [usubaStageRule_initial] using usubaInitialCode_valid (V := V)
  by_cases hs : θ = succ (⋃ˢ θ)
  · have hk : ⋃ˢ θ ∈ θ := (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hs).mpr (mem_succ_self _)
    have := IsOrdinal.of_mem hk
    have hh := usubaIterationSuccessor_valid (hs ▸ h)
    simp only [usubaStageRule, ite_eq_right hz, ite_eq_left hs]
    simpa only [← hs] using hh
  · have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
      (fun he ↦ hz he.symm)
    simpa only [usubaStageRule, ite_eq_right hz, ite_eq_right hs] using forcingInverseCode_valid h h0

theorem usubaStageRule_extends {θ s : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hz : θ ≠ ∅) :
    ForcingCodeExtends s (usubaStageRule θ s) := by
  classical
  by_cases hs : θ = succ (⋃ˢ θ)
  · simpa only [usubaStageRule, ite_eq_right hz, ite_eq_left hs] using
      usubaIterationSuccessor_extends (hs ▸ h)
  · simpa only [usubaStageRule, ite_eq_right hz, ite_eq_right hs, forcingInverseCode] using
      forcingThreadCode_extends h
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))

noncomputable def usubaIterationStep (H : V) : V :=
  usubaStageRule (domain H) (forcingIterationCodeUnion (domain H) H)

instance usubaIterationStep_definable : ℒₛₑₜ-function₁[V] usubaIterationStep := by
  unfold usubaIterationStep
  apply Language.DefinableFunction₂.comp (F := usubaStageRule)
  · definability
  · apply Language.DefinableFunction₂.comp (F := forcingIterationCodeUnion) <;> definability

theorem usubaIterationStep_valid (θ : V) (hθ : IsOrdinal θ) (H : V)
    (hH : IsForcingIterationHistory θ H) :
    IsForcingIterationCode (succ θ) (usubaIterationStep H) ∧
      ForcingCodeExtends (forcingIterationCodeUnion θ H) (usubaIterationStep H) := by
  have := hθ
  have he : usubaIterationStep H = usubaStageRule θ (forcingIterationCodeUnion θ H) := by
    simp only [usubaIterationStep, hH.table.domain_eq]
  rw [he]
  refine ⟨usubaStageRule_valid hH.union_code, ?_⟩
  by_cases hz : θ = ∅
  · subst θ
    have hz (c : V → V) (hc : ℒₛₑₜ-function₁ c) : forcingHistoryTable ∅ H c hc = ∅ := by
      ext x
      simp [forcingHistoryTable, iterationTableUnion, mem_sUnion_iff, repl_spec]
    constructor <;> simp [forcingIterationCodeUnion, hz]
  · exact usubaStageRule_extends hH.union_code hz

noncomputable def usubaCodeSequence : DefinableForcingCodeSequence V :=
  .ofRecursion usubaIterationStep usubaIterationStep_definable usubaIterationStep_valid

noncomputable def usubaForcingTower : DefinableForcingTower V :=
  (usubaCodeSequence (V := V)).tower

noncomputable def usubaIterationRec (θ : V) : V := (usubaCodeSequence (V := V)).code θ

theorem usubaIterationRec_valid (θ : V) [IsOrdinal θ] :
    IsForcingIterationCode (succ θ) (usubaIterationRec θ) :=
  (usubaCodeSequence (V := V)).valid θ inferInstance

theorem usubaIterationRec_rule (θ : V) [IsOrdinal θ] :
    usubaIterationRec θ = usubaStageRule θ
      (forcingIterationCodeUnion θ (definableGraph θ usubaIterationRec
        (usubaCodeSequence (V := V)).definable)) := by
  have he := Replacement.transfiniteRec_spec usubaIterationStep
    usubaIterationStep_definable (IsOrdinal.toOrdinal θ)
  change usubaIterationRec θ = usubaIterationStep
    (definableGraph θ usubaIterationRec (usubaCodeSequence (V := V)).definable) at he
  have hd := domain_definableGraph θ usubaIterationRec (usubaCodeSequence (V := V)).definable
  change usubaIterationRec θ = usubaStageRule
    (domain (definableGraph θ usubaIterationRec (usubaCodeSequence (V := V)).definable))
    (forcingIterationCodeUnion
      (domain (definableGraph θ usubaIterationRec (usubaCodeSequence (V := V)).definable))
      (definableGraph θ usubaIterationRec (usubaCodeSequence (V := V)).definable)) at he
  rw [hd] at he
  exact he

end ZFVP
