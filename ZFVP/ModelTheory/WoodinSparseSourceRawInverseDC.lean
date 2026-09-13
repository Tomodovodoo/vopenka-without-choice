import ZFVP.ModelTheory.WoodinSparseRawInverseDC
import ZFVP.ModelTheory.WoodinSourceRawInverseDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinSparseSourceRawInverseDC (θ : V) : Prop :=
  let θ' := woodinSourceIndex θ
  let c := woodinSparseSourcePrefixCode θ
  let γ := woodinLimitCardinal (woodinSparseSourcePrefixCardinals θ)
  ∀ p ∈ forcingInverseCodePoset θ' c,
    p ∈ forcingFormula (forcingInverseCodePoset θ' c) (forcingInverseCodeOrder θ' c)
      woodinStageCardinalFormula (standardTuple ![forcingInverseHartogsName θ' c γ])

theorem woodinSparseSourceRawInverseDC {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hzero : θ ≠ ∅) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinSparseSourceRawInverseDC θ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hzero he.symm)
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSourceCode_valid hc
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hf := woodinSourceCode_inverse_isomorphism hc
  have hraw := hc.system.inverseColumn h0 hc.subset_universe
  have hsource := hs.system.inverseColumn hz hs.subset_universe
  have ht := woodinSourceCode_inverse_top_value hc h0
  dsimp only [WoodinSparseSourceRawInverseDC]
  rw [woodinSparseSourcePrefixCardinals, woodinSourceCardinals_actual_prefix_limit hΩ hAC hsub h0]
  intro q hq
  have hp := function_value_mem hf.inverse_maps hq
  have hh := (hf.hartogs_forcing_iff hraw.order.preorder hsource.order.preorder hraw.tops.top ht hp
    woodinStageCardinalFormula).mp (woodinSparseInverseThreadsDC hΩ hAC hθ hzero hlim hn _ hp)
  simpa only [hf.value_inverse hq, woodinSparseSourcePrefixCode, forcingInverseHartogsName] using hh

end ZFVP
