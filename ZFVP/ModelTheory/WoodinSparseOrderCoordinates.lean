import ZFVP.ModelTheory.WoodinSparseSuccessorOrderCoordinates
import ZFVP.ModelTheory.WoodinSparseLimitOrderCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinSparseOrderCoordinates (θ : V) : Prop :=
  ∀ p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
    ∀ q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (succ (woodinSourceIndex θ)) p q

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableRel₅.comp

instance woodinSparseOrderCoordinates_definable : ℒₛₑₜ-predicate[V] WoodinSparseOrderCoordinates := by
  unfold WoodinSparseOrderCoordinates
  definability

theorem woodinSparseStageCode_order_coordinates_all {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    WoodinSparseOrderCoordinates θ := by
  classical
  have hall := transfinite_induction (fun ξ : V ↦ ξ ⊆ Ω → WoodinSparseOrderCoordinates ξ) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal θ) hθ
  intro ξ ih hξ p hp q hq
  have hi : ∀ i ∈ (ξ : V), WoodinSparseOrderCoordinates i := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact ih (IsOrdinal.toOrdinal i) hi (subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hξ)
  by_cases hz : (ξ : V) = ∅
  · rw [hz] at hp hq ⊢
    exact woodinSparseStageCode_initial_order_coordinates hΩ hAC hp hq
  by_cases hs : (ξ : V) = succ (⋃ˢ (ξ : V))
  · have hm : ⋃ˢ (ξ : V) ∈ (ξ : V) :=
      (congrArg (fun x : V ↦ ⋃ˢ (ξ : V) ∈ x) hs).mpr (mem_succ_self _)
    let := IsOrdinal.of_mem hm
    have hh := hi _ hm
    rw [hs] at hp hq hξ ⊢
    exact woodinSparseStageCode_successor_order_coordinates hΩ hAC hξ hh hp hq
  by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (ξ : V)))
  · exact woodinSparseStageCode_direct_order_coordinates hΩ hAC hξ hz hs hn hi hp hq
  · exact woodinSparseStageCode_inverse_order_coordinates hΩ hAC hξ hz hs hn hi hp hq

theorem woodinSparseStageCode_order_coordinates {Ω θ p q : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (succ (woodinSourceIndex θ)) p q :=
  woodinSparseStageCode_order_coordinates_all hΩ hAC hθ p hp q hq

end ZFVP
