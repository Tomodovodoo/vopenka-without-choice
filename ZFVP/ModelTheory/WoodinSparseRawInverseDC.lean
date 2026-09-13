import ZFVP.ModelTheory.WoodinSparseRawInverse
import ZFVP.ModelTheory.WoodinRawInverseDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinSparseRawInverseDC (θ : V) : Prop :=
  let c := woodinSparsePrefixCode θ
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  ∀ q ∈ woodinSparseInverseBase θ c,
    q ∈ forcingFormula (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
      woodinStageCardinalFormula
      (standardTuple ![hartogsNumberName (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (checkName ∅ γ)])

theorem woodinSparseRawInverseDC {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hzero : θ ≠ ∅) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinSparseRawInverseDC θ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hzero he.symm)
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have hc := hs.code.system.inverseColumn h0 hs.code.subset_universe
  have hN := woodinNormalized_inverse_base_laws hΩ hAC hsub h0
  have hQ := woodinSparseRawInverse_laws hΩ hAC hsub h0 hlim
  apply ((woodinNormalizationInverse_retraction hΩ hAC hsub h0).isomorphism_all_hartogs_forcing_iff
    hc.order.preorder hN.1 (fun _ hp ↦ woodinNormalizationInverse_equivalent hΩ hAC hsub h0 hp)
    hc.tops.top hN.2.1 (woodinSparseRawInverse_isomorphism hΩ hAC hsub h0 hlim) hQ.1
    (woodinSparseRawInverse_top hΩ hAC hsub h0 hlim) woodinStageCardinalFormula).mp
  exact woodinRawInverseDC hΩ hθ hzero hlim hn

theorem woodinSparseInverseThreadsDC {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hzero : θ ≠ ∅) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    ∀ p ∈ forcingInverseCodePoset θ (woodinSparsePrefixCode θ),
      p ∈ forcingFormula (forcingInverseCodePoset θ (woodinSparsePrefixCode θ))
        (forcingInverseCodeOrder θ (woodinSparsePrefixCode θ)) woodinStageCardinalFormula
        (standardTuple ![forcingInverseHartogsName θ (woodinSparsePrefixCode θ)
          (woodinLimitCardinal (woodinIterationCardinalPrefix θ))]) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hzero he.symm)
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hsp := fun i hi p hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hsub (i := i) (p := p) hi hp
  have hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ j,
      ((forcingCodeπ (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparsePrefixCode_projection hΩ hAC hsub hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  have hf := woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ
  have hs := hc.system.inverseColumn h0 hc.subset_universe
  have hQ := woodinSparseRawInverse_laws hΩ hAC hsub h0 hlim
  have ht := woodinSparseInverseFlatten_top hc h0 hsp hπ (fun _ hi ↦ woodinSparsePrefixCode_top hΩ hAC hsub hi)
  intro p hp
  apply (hf.hartogs_forcing_iff hs.order.preorder hQ.1 hs.tops.top ht hp woodinStageCardinalFormula).mpr
  exact woodinSparseRawInverseDC hΩ hAC hθ hzero hlim hn _ (function_value_mem hf.1 hp)

end ZFVP
