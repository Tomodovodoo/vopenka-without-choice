import ZFVP.ModelTheory.WoodinLocalStagePresentation
import ZFVP.ModelTheory.ForcingStageProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinLocalComparisonFormula : SetTheorySemisentence 5 :=
  f“i j k p q. !kpair.dfn
    (!value.dfn (!value.dfn (!forcingCodeEFormula (!kpair.π₁.dfn (!woodinIterationRecFormula k)))
      (!kpair.dfn i k)) p)
    (!value.dfn (!value.dfn (!forcingCodeEFormula (!kpair.π₁.dfn (!woodinIterationRecFormula k)))
      (!kpair.dfn j k)) q) ∈
    !value.dfn (!forcingCodeRFormula (!kpair.π₁.dfn (!woodinIterationRecFormula k))) k”

/-- Compare in the later of the two stages, with no endpoint parameter. -/
@[irreducible] def woodinLocalStageOrderFormula : SetTheorySemisentence 2 :=
  f“z w. ((!kpair.π₁.dfn z ⊆ !kpair.π₁.dfn w) ∧
      !woodinLocalComparisonFormula (!kpair.π₁.dfn z) (!kpair.π₁.dfn w) (!kpair.π₁.dfn w)
        (!kpair.π₂.dfn z) (!kpair.π₂.dfn w)) ∨
    ((!kpair.π₁.dfn w ⊆ !kpair.π₁.dfn z) ∧
      !woodinLocalComparisonFormula (!kpair.π₁.dfn z) (!kpair.π₁.dfn w) (!kpair.π₁.dfn z)
        (!kpair.π₂.dfn z) (!kpair.π₂.dfn w))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinLocalComparison (i j k p q : V) : Prop :=
  ⟨((forcingCodeE (kpair.π₁ (woodinIterationRec k))) ‘ ⟨i, k⟩ₖ) ‘ p,
    ((forcingCodeE (kpair.π₁ (woodinIterationRec k))) ‘ ⟨j, k⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (kpair.π₁ (woodinIterationRec k))) ‘ k

instance woodinLocalComparisonFormula_defined :
    Defined (fun v : Fin 5 → V ↦ WoodinLocalComparison (v 0) (v 1) (v 2) (v 3) (v 4))
      woodinLocalComparisonFormula :=
  ⟨fun v ↦ by simp [woodinLocalComparisonFormula, WoodinLocalComparison]⟩

def WoodinLocalStageOrder (z w : V) : Prop :=
  (kpair.π₁ z ⊆ kpair.π₁ w ∧ WoodinLocalComparison (kpair.π₁ z) (kpair.π₁ w)
    (kpair.π₁ w) (kpair.π₂ z) (kpair.π₂ w)) ∨
  (kpair.π₁ w ⊆ kpair.π₁ z ∧ WoodinLocalComparison (kpair.π₁ z) (kpair.π₁ w)
    (kpair.π₁ z) (kpair.π₂ z) (kpair.π₂ w))

instance woodinLocalStageOrderFormula_defined :
    ℒₛₑₜ-relation[V] WoodinLocalStageOrder via woodinLocalStageOrderFormula :=
  ⟨fun v ↦ by simp [woodinLocalStageOrderFormula, WoodinLocalStageOrder]⟩

/-- The local formula gives exactly the supported-thread order. -/
theorem woodinSection_order_iff_localStageOrder {δ θ i j p q : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hj : j ∈ θ)
    (hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hq : q ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ⟨forcingSectionThread θ (forcingCodeπ (woodinIterationPrefix θ))
        (forcingCodeE (woodinIterationPrefix θ)) i p,
      forcingSectionThread θ (forcingCodeπ (woodinIterationPrefix θ))
        (forcingCodeE (woodinIterationPrefix θ)) j q⟩ₖ ∈
      forcingThreadOrder θ (forcingCodeR (woodinIterationPrefix θ))
        (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
          (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
          (forcingCodeUniverse (woodinIterationPrefix θ))) ↔
      WoodinLocalStageOrder ⟨i, p⟩ₖ ⟨j, q⟩ₖ := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  simp only [WoodinLocalStageOrder, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · intro h
    rcases IsOrdinal.subset_or_supset i j with hij | hji
    · exact Or.inl ⟨hij, (woodinSection_order_iff_local hs hi hj hj hij (fun _ hx ↦ hx) hp hq).mp h⟩
    · exact Or.inr ⟨hji, (woodinSection_order_iff_local hs hi hj hi (fun _ hx ↦ hx) hji hp hq).mp h⟩
  · rintro (⟨hij, h⟩ | ⟨hji, h⟩)
    · exact (woodinSection_order_iff_local hs hi hj hj hij (fun _ hx ↦ hx) hp hq).mpr h
    · exact (woodinSection_order_iff_local hs hi hj hi (fun _ hx ↦ hx) hji hp hq).mpr h

/-- On the stage carrier the pulled-back order is the fixed local relation. -/
theorem woodinStagePullback_order_iff {δ θ z w : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hz : z ∈ forcingStageConditions θ (forcingCodeP (woodinIterationPrefix θ))
      (forcingCodeUniverse (woodinIterationPrefix θ)))
    (hw : w ∈ forcingStageConditions θ (forcingCodeP (woodinIterationPrefix θ))
      (forcingCodeUniverse (woodinIterationPrefix θ))) :
    ⟨z, w⟩ₖ ∈ forcingPullbackOrder
      (forcingStageConditions θ (forcingCodeP (woodinIterationPrefix θ))
        (forcingCodeUniverse (woodinIterationPrefix θ)))
      (forcingThreadOrder θ (forcingCodeR (woodinIterationPrefix θ))
        (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
          (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
          (forcingCodeUniverse (woodinIterationPrefix θ))))
      (forcingStageThreadMap θ (forcingCodeP (woodinIterationPrefix θ))
        (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
        (forcingCodeUniverse (woodinIterationPrefix θ))) ↔ WoodinLocalStageOrder z w := by
  rw [mem_forcingPullbackOrder_iff, forcingStageThreadMap_value hz, forcingStageThreadMap_value hw]
  simp only [hz, hw, true_and]
  obtain ⟨i, hi, p, _, hp, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hz
  obtain ⟨j, hj, q, _, hq, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hw
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
    woodinSection_order_iff_localStageOrder hs hi hj hp hq

end ZFVP
