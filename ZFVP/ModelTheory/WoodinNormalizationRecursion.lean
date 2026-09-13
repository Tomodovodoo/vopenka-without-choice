import ZFVP.ModelTheory.WoodinNormalizationInitialFamily
import ZFVP.ModelTheory.WoodinNormalizationSuccessorFamily
import ZFVP.ModelTheory.WoodinNormalizationInverseFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def woodinNormalizationRule (θ s K m : V) : V := by
  classical
  exact if θ = ∅ then woodinNormalizationInitialMap else
    if θ = succ (⋃ˢ θ) then woodinNormalizationSuccessorMap (⋃ˢ θ) s K m else
    if IsChoicelessInaccessible (woodinLimitCardinal K) then forcingNormalizationDirectMap θ s m else
      woodinNormalizationInverseMap θ s K m

instance woodinNormalizationRule_definable : ℒₛₑₜ-function₄[V] woodinNormalizationRule := by
  classical
  have h : ℒₛₑₜ-relation₅[V] (fun z θ s K m ↦
      (θ = ∅ ∧ z = woodinNormalizationInitialMap) ∨
      (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧ z = woodinNormalizationSuccessorMap (⋃ˢ θ) s K m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal K) ∧
        z = forcingNormalizationDirectMap θ s m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal K) ∧
        z = woodinNormalizationInverseMap θ s K m)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinNormalizationRule (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold woodinNormalizationRule
  split_ifs <;> tauto

noncomputable def woodinNormalizationRecursionStep (H : V) : V :=
  woodinNormalizationRule (domain H) (woodinIterationPrefix (domain H))
    (woodinIterationCardinalPrefix (domain H)) H

instance woodinNormalizationRecursionStep_definable : ℒₛₑₜ-function₁[V] woodinNormalizationRecursionStep := by
  unfold woodinNormalizationRecursionStep
  apply Language.DefinableFunction₄.comp <;> definability

noncomputable def woodinNormalizationRec (θ : V) : V :=
  Replacement.transfiniteRec woodinNormalizationRecursionStep woodinNormalizationRecursionStep_definable θ

instance woodinNormalizationRec_definable : ℒₛₑₜ-function₁[V] woodinNormalizationRec :=
  Replacement.transfiniteRec_definable woodinNormalizationRecursionStep_definable

noncomputable def woodinNormalizationHistory (θ : V) : V :=
  definableGraph θ woodinNormalizationRec woodinNormalizationRec_definable

instance woodinNormalizationHistory_definable : ℒₛₑₜ-function₁[V] woodinNormalizationHistory := by
  have h : ℒₛₑₜ-relation[V] (fun H θ ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, woodinNormalizationRec i⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinNormalizationHistory (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinNormalizationHistory, mem_definableGraph_iff]

theorem woodinNormalizationHistory_value {θ i : V} (hi : i ∈ θ) :
    (woodinNormalizationHistory θ) ‘ i = woodinNormalizationRec i := value_definableGraph _ _ _ hi

theorem woodinNormalizationHistory_empty : woodinNormalizationHistory (∅ : V) = ∅ := by
  apply mem_ext
  intro x
  simp only [woodinNormalizationHistory, mem_definableGraph_iff, not_mem_empty, false_and, exists_false]

theorem woodinNormalizationHistory_table (θ : V) : IsIterationTable θ (woodinNormalizationHistory θ) := by
  unfold woodinNormalizationHistory
  exact ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem woodinNormalizationRec_rule (θ : V) [IsOrdinal θ] :
    woodinNormalizationRec θ = woodinNormalizationRule θ (woodinIterationPrefix θ)
      (woodinIterationCardinalPrefix θ) (woodinNormalizationHistory θ) := by
  have he := Replacement.transfiniteRec_spec woodinNormalizationRecursionStep
    woodinNormalizationRecursionStep_definable (IsOrdinal.toOrdinal θ)
  change woodinNormalizationRec θ = woodinNormalizationRecursionStep
    (definableGraph θ woodinNormalizationRec woodinNormalizationRec_definable) at he
  simpa only [woodinNormalizationRecursionStep, domain_definableGraph, woodinNormalizationHistory] using he

theorem woodinNormalizationHistory_next (θ : V) :
    woodinNormalizationHistory (succ θ) =
      forcingFamilyNext θ (woodinNormalizationHistory θ) (woodinNormalizationRec θ) := by
  have hl := (woodinNormalizationHistory_table (V := V) (succ θ)).function
  have hr := (forcingFamilyNext_table θ (woodinNormalizationHistory θ) (woodinNormalizationRec θ)).function
  let := hl
  let := hr
  apply functions_eq_of_domain_values
  · rw [(woodinNormalizationHistory_table _).domain_eq, (forcingFamilyNext_table _ _ _).domain_eq]
  intro i hi
  rw [(woodinNormalizationHistory_table _).domain_eq] at hi
  rw [woodinNormalizationHistory_value hi]
  rcases mem_succ_iff.mp hi with rfl | hi
  · rw [forcingFamilyNext_new]
  · rw [forcingFamilyNext_old hi, woodinNormalizationHistory_value hi]

end ZFVP
