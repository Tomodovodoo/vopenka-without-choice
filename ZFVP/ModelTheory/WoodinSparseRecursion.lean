import ZFVP.ModelTheory.WoodinRecodingHistory
import ZFVP.ModelTheory.WoodinSparseInitial
import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.ModelTheory.WoodinSparseInverseStage
import ZFVP.ModelTheory.WoodinSparseDirectTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def woodinSparseRecodingInitialRow : V :=
  ⟨woodinSparseInitialCarrier, ⟨woodinSparseInitialOrder, woodinSparseInitialMap⟩ₖ⟩ₖ

noncomputable def woodinSparseRecodingSuccessorRow (k c m : V) : V :=
  ⟨woodinSparseSuccessorCarrier k c, ⟨woodinSparseSuccessorOrder k c, woodinSparseSuccessorMap k c m⟩ₖ⟩ₖ

noncomputable def woodinSparseRecodingDirectRow (θ c m : V) : V :=
  ⟨woodinSparseDirectBase θ c,
    ⟨woodinSparseDirectOrder θ c, woodinSparseDirectMap θ c m⟩ₖ⟩ₖ

noncomputable def woodinSparseRecodingInverseRow (θ c m : V) : V :=
  ⟨woodinSparseCompletedInverseCarrier θ c, ⟨woodinSparseCompletedInverseOrder θ c, woodinSparseCompletedInverseMap θ c m⟩ₖ⟩ₖ

instance woodinSparseRecodingInitialRow_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinSparseRecodingInitialRow : V) := by
  unfold woodinSparseRecodingInitialRow
  definability

instance woodinSparseRecodingSuccessorRow_definable : ℒₛₑₜ-function₃[V] woodinSparseRecodingSuccessorRow := by
  unfold woodinSparseRecodingSuccessorRow
  definability

instance woodinSparseRecodingDirectRow_definable : ℒₛₑₜ-function₃[V] woodinSparseRecodingDirectRow := by
  unfold woodinSparseRecodingDirectRow
  definability

instance woodinSparseRecodingInverseRow_definable : ℒₛₑₜ-function₃[V] woodinSparseRecodingInverseRow := by
  unfold woodinSparseRecodingInverseRow
  definability

noncomputable def woodinSparseRecodingRowRule (θ c m : V) : V := by
  classical
  exact if θ = ∅ then woodinSparseRecodingInitialRow
    else if θ = succ (⋃ˢ θ) then woodinSparseRecodingSuccessorRow (⋃ˢ θ) c m
    else if IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) then
      woodinSparseRecodingDirectRow θ c m
    else woodinSparseRecodingInverseRow θ c m

instance woodinSparseRecodingRowRule_definable : ℒₛₑₜ-function₃[V] woodinSparseRecodingRowRule := by
  classical
  have h : ℒₛₑₜ-relation₄[V] (fun z θ c m ↦
      (θ = ∅ ∧ z = woodinSparseRecodingInitialRow) ∨
      (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧ z = woodinSparseRecodingSuccessorRow (⋃ˢ θ) c m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
        z = woodinSparseRecodingDirectRow θ c m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
        z = woodinSparseRecodingInverseRow θ c m)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseRecodingRowRule (v 1) (v 2) (v 3) ↔ _
  unfold woodinSparseRecodingRowRule
  split_ifs <;> tauto

noncomputable def woodinSparseRecodingRule (θ Q T m : V) : V :=
  woodinSparseRecodingRowRule θ (forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m) m

instance woodinSparseRecodingRule_definable : ℒₛₑₜ-function₄[V] woodinSparseRecodingRule := by
  unfold woodinSparseRecodingRule
  apply Language.DefinableFunction₃.comp
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · definability

noncomputable def woodinSparseRecodingStep (H : V) : V :=
  woodinSparseRecodingRule (domain H) (woodinRecodingCarriers H) (woodinRecodingOrders H) (woodinRecodingMaps H)

instance woodinSparseRecodingStep_definable : ℒₛₑₜ-function₁[V] woodinSparseRecodingStep := by
  unfold woodinSparseRecodingStep
  apply Language.DefinableFunction₄.comp <;> definability

noncomputable def woodinSparseRecodingRec (θ : V) : V :=
  Replacement.transfiniteRec woodinSparseRecodingStep woodinSparseRecodingStep_definable θ

instance woodinSparseRecodingRec_definable : ℒₛₑₜ-function₁[V] woodinSparseRecodingRec :=
  Replacement.transfiniteRec_definable woodinSparseRecodingStep_definable

noncomputable def woodinSparseRecodingHistory (θ : V) : V :=
  definableGraph θ woodinSparseRecodingRec woodinSparseRecodingRec_definable

instance woodinSparseRecodingHistory_definable : ℒₛₑₜ-function₁[V] woodinSparseRecodingHistory := by
  have h : ℒₛₑₜ-relation[V] (fun H θ ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, woodinSparseRecodingRec i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseRecodingHistory (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseRecodingHistory, mem_definableGraph_iff]

theorem woodinSparseRecodingRec_rule (θ : V) [IsOrdinal θ] :
    woodinSparseRecodingRec θ = woodinSparseRecodingRule θ (woodinRecodingCarriers (woodinSparseRecodingHistory θ))
      (woodinRecodingOrders (woodinSparseRecodingHistory θ)) (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  have he := Replacement.transfiniteRec_spec woodinSparseRecodingStep woodinSparseRecodingStep_definable (IsOrdinal.toOrdinal θ)
  change woodinSparseRecodingRec θ = woodinSparseRecodingStep (definableGraph θ woodinSparseRecodingRec woodinSparseRecodingRec_definable) at he
  simpa only [woodinSparseRecodingStep, woodinSparseRecodingHistory, domain_definableGraph] using he

theorem woodinSparseRecodingHistory_value {θ i : V} (hi : i ∈ θ) :
    (woodinSparseRecodingHistory θ) ‘ i = woodinSparseRecodingRec i := value_definableGraph _ _ _ hi

end ZFVP
