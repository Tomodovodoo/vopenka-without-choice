import ZFVP.ModelTheory.WoodinRecodedInitial
import ZFVP.ModelTheory.WoodinRecodedDirectNext

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodingCarriers (H : V) : V :=
  definableGraph (domain H) (fun i ↦ kpair.π₁ (H ‘ i)) (by definability)

noncomputable def woodinRecodingOrders (H : V) : V :=
  definableGraph (domain H) (fun i ↦ kpair.π₁ (kpair.π₂ (H ‘ i))) (by definability)

noncomputable def woodinRecodingMaps (H : V) : V :=
  definableGraph (domain H) (fun i ↦ kpair.π₂ (kpair.π₂ (H ‘ i))) (by definability)

instance woodinRecodingCarriers_definable : ℒₛₑₜ-function₁[V] woodinRecodingCarriers := by
  have h : ℒₛₑₜ-relation[V] (fun Q H ↦ ∀ z, z ∈ Q ↔ ∃ i ∈ domain H, z = ⟨i, kpair.π₁ (H ‘ i)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinRecodingCarriers (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinRecodingCarriers, mem_definableGraph_iff]

instance woodinRecodingOrders_definable : ℒₛₑₜ-function₁[V] woodinRecodingOrders := by
  have h : ℒₛₑₜ-relation[V] (fun T H ↦ ∀ z, z ∈ T ↔ ∃ i ∈ domain H, z = ⟨i, kpair.π₁ (kpair.π₂ (H ‘ i))⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinRecodingOrders (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinRecodingOrders, mem_definableGraph_iff]

instance woodinRecodingMaps_definable : ℒₛₑₜ-function₁[V] woodinRecodingMaps := by
  have h : ℒₛₑₜ-relation[V] (fun m H ↦ ∀ z, z ∈ m ↔ ∃ i ∈ domain H, z = ⟨i, kpair.π₂ (kpair.π₂ (H ‘ i))⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinRecodingMaps (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinRecodingMaps, mem_definableGraph_iff]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def woodinRecodingInitialRow : V :=
  ⟨woodinRecodedInitialCarrier, ⟨woodinRecodedInitialOrder, identity woodinRecodedInitialCarrier⟩ₖ⟩ₖ

noncomputable def woodinRecodingSuccessorRow (k c m : V) : V :=
  ⟨woodinRecodedSuccessorCarrier k c, ⟨woodinRecodedSuccessorOrder k c, woodinRecodedSuccessorMap k c m⟩ₖ⟩ₖ

noncomputable def woodinRecodingDirectRow (θ c m : V) : V :=
  ⟨forcingSparseCodes θ c (forcingCodeUniverse c),
    ⟨forcingSparseOrder θ c (forcingCodeUniverse c), woodinRecodedDirectMap θ c m⟩ₖ⟩ₖ

noncomputable def woodinRecodingInverseRow (θ c m : V) : V :=
  ⟨woodinRecodedInverseCarrier θ c, ⟨woodinRecodedInverseOrder θ c, woodinRecodedInverseMap θ c m⟩ₖ⟩ₖ

instance woodinRecodingInitialRow_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinRecodingInitialRow : V) := by
  unfold woodinRecodingInitialRow
  definability

instance woodinRecodingSuccessorRow_definable : ℒₛₑₜ-function₃[V] woodinRecodingSuccessorRow := by
  unfold woodinRecodingSuccessorRow
  definability

instance woodinRecodingDirectRow_definable : ℒₛₑₜ-function₃[V] woodinRecodingDirectRow := by
  unfold woodinRecodingDirectRow forcingCodeUniverse
  definability

instance woodinRecodingInverseRow_definable : ℒₛₑₜ-function₃[V] woodinRecodingInverseRow := by
  unfold woodinRecodingInverseRow
  definability

noncomputable def woodinRecodingRowRule (θ c m : V) : V := by
  classical
  exact if θ = ∅ then woodinRecodingInitialRow
    else if θ = succ (⋃ˢ θ) then woodinRecodingSuccessorRow (⋃ˢ θ) c m
    else if IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) then
      woodinRecodingDirectRow θ c m
    else woodinRecodingInverseRow θ c m

instance woodinRecodingRowRule_definable : ℒₛₑₜ-function₃[V] woodinRecodingRowRule := by
  classical
  have h : ℒₛₑₜ-relation₄[V] (fun z θ c m ↦
      (θ = ∅ ∧ z = woodinRecodingInitialRow) ∨
      (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧ z = woodinRecodingSuccessorRow (⋃ˢ θ) c m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
        z = woodinRecodingDirectRow θ c m) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
        z = woodinRecodingInverseRow θ c m)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinRecodingRowRule (v 1) (v 2) (v 3) ↔ _
  unfold woodinRecodingRowRule
  split_ifs <;> tauto

noncomputable def woodinRecodingRule (θ Q T m : V) : V :=
  woodinRecodingRowRule θ (forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m) m

instance woodinRecodingRule_definable : ℒₛₑₜ-function₄[V] woodinRecodingRule := by
  unfold woodinRecodingRule
  apply Language.DefinableFunction₃.comp
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · definability

noncomputable def woodinRecodingStep (H : V) : V :=
  woodinRecodingRule (domain H) (woodinRecodingCarriers H) (woodinRecodingOrders H) (woodinRecodingMaps H)

instance woodinRecodingStep_definable : ℒₛₑₜ-function₁[V] woodinRecodingStep := by
  unfold woodinRecodingStep
  apply Language.DefinableFunction₄.comp <;> definability

noncomputable def woodinRecodingRec (θ : V) : V :=
  Replacement.transfiniteRec woodinRecodingStep woodinRecodingStep_definable θ

instance woodinRecodingRec_definable : ℒₛₑₜ-function₁[V] woodinRecodingRec :=
  Replacement.transfiniteRec_definable woodinRecodingStep_definable

noncomputable def woodinRecodingHistory (θ : V) : V :=
  definableGraph θ woodinRecodingRec woodinRecodingRec_definable

instance woodinRecodingHistory_definable : ℒₛₑₜ-function₁[V] woodinRecodingHistory := by
  have h : ℒₛₑₜ-relation[V] (fun H θ ↦ ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = ⟨i, woodinRecodingRec i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinRecodingHistory (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinRecodingHistory, mem_definableGraph_iff]

theorem woodinRecodingRec_rule (θ : V) [IsOrdinal θ] :
    woodinRecodingRec θ = woodinRecodingRule θ (woodinRecodingCarriers (woodinRecodingHistory θ))
      (woodinRecodingOrders (woodinRecodingHistory θ)) (woodinRecodingMaps (woodinRecodingHistory θ)) := by
  have he := Replacement.transfiniteRec_spec woodinRecodingStep woodinRecodingStep_definable (IsOrdinal.toOrdinal θ)
  change woodinRecodingRec θ = woodinRecodingStep (definableGraph θ woodinRecodingRec woodinRecodingRec_definable) at he
  simpa only [woodinRecodingStep, woodinRecodingHistory, domain_definableGraph] using he

theorem woodinRecodingHistory_value {θ i : V} (hi : i ∈ θ) :
    (woodinRecodingHistory θ) ‘ i = woodinRecodingRec i := value_definableGraph _ _ _ hi

end ZFVP
