import ZFVP.ModelTheory.SchmerlFiniteDomainCoverage
import ZFVP.ModelTheory.SchmerlInfinitarySmallDeadEnd

/-! Full weak Rubinness from the strengthened standard-Q sentence. Its coding
conclusion applies to every maximal filter in the original contract. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order
open ZFVP.Infinitary (Formula)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SelectedDomainClauses.hasCofinalOmegaOneChain {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) :
    HasCofinalOmegaOneChain (fun x ↦ x ∈ finiteSubsets s) := by
  let : LinearOrder {d // D d} := h.order
  have hcof : Order.cof {d // D d} = Cardinal.aleph 1 := by
    apply le_antisymm
    · have hc := Order.cof_le (show IsCofinal (Set.univ : Set {d // D d}) from
        fun d ↦ ⟨d, Set.mem_univ d, le_rfl⟩)
      have hm : Cardinal.mk {d // D d} ≤ Cardinal.aleph 1 :=
        (Cardinal.mk_subtype_le D).trans hcard
      exact hc.trans (by simpa using hm)
    · exact Cardinal.aleph_one_le_iff.mpr h.uncountable_cofinality
  obtain ⟨c, hc⟩ := exists_omegaOne_cofinal_embedding hcof
  refine ⟨fun i ↦ (c i).val, ?_, ?_, ?_⟩
  · intro i
    exact (mem_finiteSubsets_iff s _).mpr
      ⟨(h.finite _ (c i).property).2, (h.finite _ (c i).property).1⟩
  · intro i j hij
    refine ⟨c.monotone hij.le, ?_⟩
    intro he
    exact (ne_of_lt (c.strictMono hij)) (Subtype.ext he)
  · intro a ha
    obtain ⟨has, hfin⟩ := (mem_finiteSubsets_iff s a).mp ha
    obtain ⟨d, hd, had⟩ := h.cofinal a hfin has
    obtain ⟨e, ⟨i, rfl⟩, hde⟩ := hc (⟨d, hd⟩ : {d // D d})
    exact ⟨i, SetTheory.subset_trans had hde⟩

/-- Φ⁺ supplies the missing coverage condition and therefore the entire E05
property, not just codes for already selected branch filters. -/
theorem isWeaklyRubin_of_weaklyRubinSentence
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![])
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) : IsWeaklyRubin V := by
  obtain ⟨hdead, hsmall⟩ := (eval_weaklyRubinSentence S hS).mp h
  refine ⟨ratherClassless_of_deadEndSentence S hS hdead, fun s hs ↦ ?_⟩
  have hf := (Formula.eval_and _ _ _).mp hdead |>.2
  have hdata := (eval_functionTreeFamilySentence deadEndSetEmbedding S hS
    functionSelected functionColor).mp hf s hs
  obtain ⟨hD, hcodes⟩ := filters_coded_of_functionTreeDataClause deadEndSetEmbedding S hS
    functionSelected functionColor s hdata
  let : LinearOrder {d // @Formula.Eval deadEndLanguage V S 2 functionSelected ![s, d]} := hD.order
  refine ⟨hD.hasCofinalOmegaOneChain hcard, fun F hF hchain ↦ ?_⟩
  obtain ⟨B, hB, hBF⟩ := hsmall.maximal_filter_is_branch_filter hF hchain hD.chain
  obtain ⟨m, hm⟩ := hcodes B hB
  exact ⟨m, fun p ↦ (hm p).trans (congrFun hBF p ▸ Iff.rfl)⟩

/-- Size reduction and full extraction preserve any supplied first-order
theory. The source expansion must actually satisfy Φ⁺. -/
theorem exists_small_weaklyRubin_model (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![]) :
    ∃ N : Type, ∃ _ : SetStructure N, ∃ _ : Nonempty N, ∃ _ : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      N↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk N = Cardinal.aleph 1 ∧
        IsWeaklyRubin N ∧ IsZFDeadEnd N ∧ FinSmall N := by
  obtain ⟨N, hNS, hne, hZF, hT, hcard, hdead, hfin, SN, hSN, hsent⟩ :=
    exists_small_weaklyRubinSentence_model T S hS h
  let : SetStructure N := hNS
  let : Nonempty N := hne
  let : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hZF
  exact ⟨N, hNS, hne, hZF, hT, hcard,
    isWeaklyRubin_of_weaklyRubinSentence SN hSN hsent hcard.le, hdead, hfin⟩

end ZFVP.Schmerl
