import ZFVP.ModelTheory.WoodinBoundInvariant
import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ i p α j : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
include hs hi

theorem woodinQuotientSequence_semantics
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G) :
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    IsForcingDescending
      (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
      (A.check α) (A.ofName f) := by
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hi).code.system.order.preorder i (mem_succ_self i),
    (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
  have hπ := (woodinInverseCoordinate_split hs hi).projection
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)] at hπ
  have h0 : (∅ : V) ∈ θ := by
    let := IsOrdinal.of_mem hi
    rcases IsOrdinal.subset_iff.mp (empty_subset i) with he | he
    · exact he.symm ▸ hi
    · exact IsOrdinal.toIsTransitive.mem_trans he hi
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hD := (hc.system.inverseColumn h0 hc.subset_universe).order.preorder
  exact A.projectionQuotient_descending_of_forced hπ hD f hpG hf

theorem woodinQuotientBoundAt_iff_generics [Countable V]
    (hj : j ∈ θ) (hij : i ⊆ j)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)) :
    IsWoodinQuotientBoundAt θ i p f.val α j ↔
      woodinQuotientBoundRec θ i p f.val j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j ∧
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G), p ∈ G →
      let A : ForcingContext V := ⟨_, _, _, G,
        (hs i hi).code.system.order.preorder i (mem_succ_self i),
        (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
      let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
      A.check (woodinQuotientBoundRec θ i p f.val j) ∈
        A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ∧
      ∀ a ∈ A.check α, ⟨A.check (woodinQuotientBoundRec θ i p f.val j), (A.ofName μ) ‘ a⟩ₖ ∈
        forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ)) := by
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hπ := hc.system.projection hi hj hij
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)] at hπ
  have hS := hc.system.order.preorder j hj
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro G hG hpG
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    exact A.projectionQuotient_bound_of_forced hπ hS μ hpG (h.2 hij)
  · rintro ⟨hm, hb⟩
    refine ⟨hm, fun _ ↦ ?_⟩
    exact projectionQuotient_bound_forced_of_generics
      ((hs i hi).code.system.order.preorder i (mem_succ_self i))
      ((hs i hi).code.system.tops.top i (mem_succ_self i)) hπ hS hp μ hb

end ZFVP
