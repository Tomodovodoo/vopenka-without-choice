import ZFVP.ModelTheory.WoodinStageRule
import ZFVP.ModelTheory.WoodinIterationHistory
import ZFVP.SetTheory.UniformRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinHistoryCardinalUnion_definable :
    ℒₛₑₜ-function₂[V] woodinHistoryCardinalUnion :=
  forcingHistoryTable_definable (fun x : V ↦ x) (by definability)

noncomputable def woodinHistoryCodes (H : V) : V :=
  definableGraph (domain H) (fun i ↦ kpair.π₁ (H ‘ i)) (by definability)

noncomputable def woodinHistoryCardinals (H : V) : V :=
  definableGraph (domain H) (fun i ↦ kpair.π₂ (H ‘ i)) (by definability)

instance woodinHistoryCodes_definable : ℒₛₑₜ-function₁[V] woodinHistoryCodes := by
  have h : ℒₛₑₜ-relation (fun g H : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ domain H, z = ⟨i, kpair.π₁ (H ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinHistoryCodes (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinHistoryCodes, mem_definableGraph_iff]

instance woodinHistoryCardinals_definable : ℒₛₑₜ-function₁[V] woodinHistoryCardinals := by
  have h : ℒₛₑₜ-relation (fun g H : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ domain H, z = ⟨i, kpair.π₂ (H ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinHistoryCardinals (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinHistoryCardinals, mem_definableGraph_iff]

noncomputable def woodinIterationRecursionStep (H : V) : V :=
  woodinStageRule (domain H) (forcingIterationCodeUnion (domain H) (woodinHistoryCodes H))
    (woodinHistoryCardinalUnion (domain H) (woodinHistoryCardinals H))

instance woodinIterationRecursionStep_definable : ℒₛₑₜ-function₁[V] woodinIterationRecursionStep := by
  unfold woodinIterationRecursionStep
  apply Language.DefinableFunction₃.comp (F := woodinStageRule)
  · definability
  · apply Language.DefinableFunction₂.comp (F := forcingIterationCodeUnion) <;> definability
  · apply Language.DefinableFunction₂.comp (F := woodinHistoryCardinalUnion) <;> definability

noncomputable def woodinIterationRec (θ : V) : V :=
  Replacement.transfiniteRec woodinIterationRecursionStep woodinIterationRecursionStep_definable θ

instance woodinIterationRec_definable : ℒₛₑₜ-function₁[V] woodinIterationRec :=
  Replacement.transfiniteRec_definable woodinIterationRecursionStep_definable

noncomputable def woodinIterationHistory (θ : V) : V :=
  definableGraph θ woodinIterationRec woodinIterationRec_definable

instance woodinIterationHistory_definable : ℒₛₑₜ-function₁[V] woodinIterationHistory := by
  have h : ℒₛₑₜ-relation (fun H θ : V ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, woodinIterationRec i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinIterationHistory (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinIterationHistory, mem_definableGraph_iff]

noncomputable def woodinIterationPrefix (θ : V) : V :=
  forcingIterationCodeUnion θ (woodinHistoryCodes (woodinIterationHistory θ))

noncomputable def woodinIterationCardinalPrefix (θ : V) : V :=
  woodinHistoryCardinalUnion θ (woodinHistoryCardinals (woodinIterationHistory θ))

instance woodinIterationPrefix_definable : ℒₛₑₜ-function₁[V] woodinIterationPrefix := by
  unfold woodinIterationPrefix
  apply Language.DefinableFunction₂.comp (F := forcingIterationCodeUnion) <;> definability

instance woodinIterationCardinalPrefix_definable : ℒₛₑₜ-function₁[V] woodinIterationCardinalPrefix := by
  unfold woodinIterationCardinalPrefix
  apply Language.DefinableFunction₂.comp (F := woodinHistoryCardinalUnion) <;> definability

theorem woodinIterationRec_rule (θ : V) [IsOrdinal θ] :
    woodinIterationRec θ = woodinStageRule θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) := by
  have he := Replacement.transfiniteRec_spec woodinIterationRecursionStep
    woodinIterationRecursionStep_definable (IsOrdinal.toOrdinal θ)
  change woodinIterationRec θ = woodinIterationRecursionStep
    (definableGraph θ woodinIterationRec woodinIterationRec_definable) at he
  simpa only [woodinIterationRecursionStep, domain_definableGraph,
    woodinIterationHistory, woodinIterationPrefix, woodinIterationCardinalPrefix] using he

theorem woodinIterationRec_initial :
    woodinIterationRec (∅ : V) = ⟨woodinInitialCode, woodinInitialCardinals⟩ₖ := by
  rw [woodinIterationRec_rule, woodinStageRule_initial]

theorem woodinIterationRec_successor (k : V) [IsOrdinal k] :
    woodinIterationRec (succ k) =
      ⟨woodinIterationSuccessor k (woodinIterationPrefix (succ k)) (woodinIterationCardinalPrefix (succ k)),
        woodinIterationCardinalNext k (woodinIterationPrefix (succ k)) (woodinIterationCardinalPrefix (succ k))⟩ₖ := by
  rw [woodinIterationRec_rule, woodinStageRule_successor]

theorem woodinIterationRec_direct {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
    (hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinIterationRec θ = ⟨forcingDirectCode θ (woodinIterationPrefix θ),
      forcingFamilyNext θ (woodinIterationCardinalPrefix θ)
        (woodinLimitCardinal (woodinIterationCardinalPrefix θ))⟩ₖ := by
  rw [woodinIterationRec_rule]
  simp only [woodinStageRule, ite_eq_right h0, ite_eq_right hs, ite_eq_left hi]

theorem woodinIterationRec_inverse {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
    (hi : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinIterationRec θ =
      ⟨woodinInverseSourceCode θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ),
        woodinInverseCardinalNext θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ)⟩ₖ := by
  rw [woodinIterationRec_rule]
  simp only [woodinStageRule, ite_eq_right h0, ite_eq_right hs, ite_eq_right hi]

end ZFVP
