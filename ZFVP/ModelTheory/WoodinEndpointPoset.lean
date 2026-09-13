import ZFVP.ModelTheory.WoodinIterationContract
import ZFVP.ModelTheory.LimitSplitProjection
import ZFVP.ModelTheory.IterationSystemProjection
import ZFVP.ModelTheory.LimitCodeDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The endpoint code of Woodin's iteration at `δ`: the direct limit stage taken
over the whole index ordinal `δ`, appended to the prefix code. -/
noncomputable def woodinEndpointCode (δ : V) : V :=
  forcingDirectCode δ (woodinIterationPrefix δ)

/-- The endpoint forcing `Q_δ`: the poset sitting at index `δ` in the endpoint code. -/
noncomputable def woodinEndpointPoset (δ : V) : V :=
  (forcingCodeP (woodinEndpointCode δ)) ‘ δ

/-- The order of the endpoint forcing. -/
noncomputable def woodinEndpointOrder (δ : V) : V :=
  (forcingCodeR (woodinEndpointCode δ)) ‘ δ

/-- The largest condition of the endpoint forcing. -/
noncomputable def woodinEndpointTop (δ : V) : V :=
  (forcingCodet (woodinEndpointCode δ)) ‘ δ

@[simp] theorem woodinEndpointPoset_eq (δ : V) :
    woodinEndpointPoset δ = forcingDirectLimit δ (forcingCodeP (woodinIterationPrefix δ))
      (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ))
      (forcingCodeUniverse (woodinIterationPrefix δ)) := by
  simp only [woodinEndpointPoset, woodinEndpointCode, forcingDirectCode,
    forcingThreadCode_poset]

@[simp] theorem woodinEndpointOrder_eq (δ : V) :
    woodinEndpointOrder δ = forcingThreadOrder δ (forcingCodeR (woodinIterationPrefix δ))
      (forcingDirectLimit δ (forcingCodeP (woodinIterationPrefix δ))
        (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ))
        (forcingCodeUniverse (woodinIterationPrefix δ))) := by
  simp only [woodinEndpointOrder, woodinEndpointCode, forcingDirectCode,
    forcingThreadCode_order]

@[simp] theorem woodinEndpointTop_eq (δ : V) :
    woodinEndpointTop δ = forcingSectionThread δ (forcingCodeπ (woodinIterationPrefix δ))
      (forcingCodeE (woodinIterationPrefix δ)) ∅
      ((forcingCodet (woodinIterationPrefix δ)) ‘ ∅) := by
  simp only [woodinEndpointTop, woodinEndpointCode, forcingDirectCode,
    forcingThreadCode_top]

/-- Every stage poset of an iteration code sits inside the code's universe set.
This is the `hU` side condition of the direct limit lemmas. -/
theorem forcingCodeP_subset_universe {θ s : V} (h : IsForcingIterationCode θ s) :
    ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ forcingCodeUniverse s := h.subset_universe

theorem woodinEndpointPoset_preorder {δ : V}
    (h : IsWoodinIteration δ δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ)) :
    IsForcingPreorder (woodinEndpointPoset δ) (woodinEndpointOrder δ) := by
  rw [woodinEndpointPoset_eq, woodinEndpointOrder_eq]
  exact forcingDirectLimit_preorder h.code.system.order.preorder

/-- Each stage `k < δ` embeds into the endpoint forcing as a complete subforcing:
the coordinate map at `k` is a projection and the section map at `k` is its exact
right inverse. -/
theorem woodinEndpoint_splitProjection {δ k : V} [IsOrdinal δ]
    (h : IsWoodinIteration δ δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ))
    (hk : k ∈ δ) :
    IsForcingSplitProjection ((forcingCodeP (woodinIterationPrefix δ)) ‘ k)
      ((forcingCodeR (woodinIterationPrefix δ)) ‘ k)
      (woodinEndpointPoset δ) (woodinEndpointOrder δ)
      (forcingThreadCoordinate (woodinEndpointPoset δ) k)
      (forcingThreadSection δ (forcingCodeP (woodinIterationPrefix δ))
        (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ)) k) := by
  rw [woodinEndpointPoset_eq, woodinEndpointOrder_eq]
  exact forcingDirectLimit_splitProjection h.code.system.split hk
    (forcingCodeP_subset_universe h.code)
    (fun i hi j hj hij ↦ h.code.system.splitProjection hi hj hij)

theorem woodinEndpointTop_isTop {δ : V} [IsOrdinal δ]
    (h : IsWoodinIteration δ δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ))
    (h0 : (∅ : V) ∈ δ) :
    IsForcingTop (woodinEndpointPoset δ) (woodinEndpointOrder δ) (woodinEndpointTop δ) :=
  (forcingDirectCode_valid h.code h0).system.tops.top δ (mem_succ_self δ)

instance woodinEndpointCode_definable : ℒₛₑₜ-function₁[V] woodinEndpointCode := by
  unfold woodinEndpointCode
  apply Language.DefinableFunction₂.comp (F := forcingDirectCode) <;> definability

instance woodinEndpointPoset_definable : ℒₛₑₜ-function₁[V] woodinEndpointPoset := by
  unfold woodinEndpointPoset
  definability

instance woodinEndpointOrder_definable : ℒₛₑₜ-function₁[V] woodinEndpointOrder := by
  unfold woodinEndpointOrder
  definability

instance woodinEndpointTop_definable : ℒₛₑₜ-function₁[V] woodinEndpointTop := by
  unfold woodinEndpointTop
  definability

end ZFVP
