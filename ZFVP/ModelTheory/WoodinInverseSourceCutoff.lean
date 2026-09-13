import ZFVP.ModelTheory.WoodinLimitCardinals
import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.StrictHartogsCutoffTransfer
import ZFVP.ModelTheory.ForcingHartogsChoice
import ZFVP.SetTheory.ForcingThreadUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.inverse_small {δ θ s K c : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hc : IsChoicelessInaccessible c)
    (hθ : θ ∈ c) (hK : ∀ i ∈ θ, K ‘ i ∈ c) :
    forcingInverseCodePoset θ s ∈ hierarchy c ∧ forcingInverseCodeOrder θ s ∈ hierarchy c := by
  let := hc.1
  have hp : forcingCodeP s ∈ hierarchy c ^ θ := h.code.tableP.mem_function (by
    intro i hi
    have hs := h.small i hi
    have hb : woodinStageCardinal (woodinIterationStage s K i) ∈ c := by
      simpa [woodinIterationStage] using hK i hi
    simpa [woodinIterationStage] using hs c hc hb)
  exact forcingInverseLimit_small_family hc (ordinal_mem_hierarchy_iff.mpr hθ) hp

theorem IsWoodinIteration.inverse_sourceCutoff {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    forcingInverseSourceCutoff θ s (woodinLimitCardinal K) ∈ δ ∧
    IsWoodinNamedPrefixCutoff (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseHartogsName θ s (woodinLimitCardinal K))
      (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) := by
  let := hδ.inaccessible.1
  let := h.limitCardinal_ordinal
  have hs := h.inverse_small hδ.inaccessible hθ h.bounded
  have hb := h.limitCardinal_below hδ.inaccessible.regular hθ
  have c := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  obtain ⟨b, hbδ, hcut⟩ := hδ.strictHartogsPrefixCutoff c.order.preorder ht hs.1 hs.2 hb
    (fun p hp ↦ hartogsNumberName_forces_regular c.order.preorder ht hp τ (hγ p hp) (hDC p hp))
    (fun p hp ↦ hartogsNumberName_forces_dependentChoiceBelow c.order.preorder ht hp τ
      (forces_checked_ordinal c.order.preorder ht inferInstance hp) (hDC p hp))
  have hc := (forcingInverseSourceCutoff_spec hcut).2.1
  let := IsOrdinal.of_mem hbδ
  refine ⟨?_, hc⟩
  exact ordinal_mem_of_subset_mem (woodinNamedPrefixCutoff_le hcut) hbδ

theorem IsWoodinIteration.inverse_small_above_limit {δ θ s K c : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hc : IsChoicelessInaccessible c) (hγc : woodinLimitCardinal K ∈ c) :
    forcingInverseCodePoset θ s ∈ hierarchy c ∧ forcingInverseCodeOrder θ s ∈ hierarchy c := by
  let := hc.1
  let := h.limitCardinal_ordinal
  apply h.inverse_small hc (ordinal_mem_of_subset_mem (h.index_subset_limit hlim) hγc)
  intro i hi
  let := (h.inaccessible i hi).1
  exact ordinal_mem_of_subset_mem (h.cardinal_subset_limit hi) hγc

end ZFVP
