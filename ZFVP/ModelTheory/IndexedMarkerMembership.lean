import ZFVP.ModelTheory.NamedMembershipEmbedding

/-! Membership structures with constants for a transitive base and an indexed family of markers.
The marker labelled by j uses the symbol (B,j), disjoint from the base symbols. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def markerIndexSet (B n : V) : V := B ∪ (({B} : V) ×ˢ n)

instance markerIndexSet_definable : ℒₛₑₜ-function₂[V] markerIndexSet := by
  unfold markerIndexSet
  definability

noncomputable def indexedMarkerValue (B c i : V) : V := by
  classical
  exact if i ∈ B then i else c ‘ (kpair.π₂ i)

instance indexedMarkerValue_definable : ℒₛₑₜ-function₃[V] indexedMarkerValue := by
  have hd : ℒₛₑₜ-relation₄[V] (fun y B c i ↦
      (i ∈ B ∧ y = i) ∨ (i ∉ B ∧ y = c ‘ (kpair.π₂ i))) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = indexedMarkerValue (v 1) (v 2) (v 3) ↔ _
  unfold indexedMarkerValue
  split_ifs <;> simp_all

noncomputable def indexedMarkerNames (B n c : V) : V :=
  definableGraph (markerIndexSet B n) (indexedMarkerValue B c) (by definability)

instance indexedMarkerNames_definable : ℒₛₑₜ-function₃[V] indexedMarkerNames := by
  have hd : ℒₛₑₜ-relation₄[V] (fun F B n c ↦
      ∀ p, p ∈ F ↔ ∃ i ∈ markerIndexSet B n, p = ⟨i, indexedMarkerValue B c i⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = indexedMarkerNames (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [indexedMarkerNames, mem_definableGraph_iff]

theorem markerIndexSet_base {B n i : V} (hi : i ∈ B) : i ∈ markerIndexSet B n :=
  mem_union_iff.mpr (Or.inl hi)

theorem markerIndexSet_marker {B n j : V} (hj : j ∈ n) : ⟨B, j⟩ₖ ∈ markerIndexSet B n :=
  mem_union_iff.mpr (Or.inr (mem_prod_iff.mpr ⟨B, by simp, j, hj, rfl⟩))

theorem markerSymbol_not_mem_base (B j : V) [IsTransitive B] : ⟨B, j⟩ₖ ∉ B := by
  intro hp
  exact mem_irrefl B (kpair_components_mem_transitive hp).1

theorem indexedMarkerNames_base {B n c i : V} (hi : i ∈ B) :
    (indexedMarkerNames B n c) ‘ i = i := by
  rw [indexedMarkerNames, value_definableGraph _ _ _ (markerIndexSet_base hi)]
  simp [indexedMarkerValue, hi]

theorem indexedMarkerNames_marker {B n c j : V} [IsTransitive B] (hj : j ∈ n) :
    (indexedMarkerNames B n c) ‘ ⟨B, j⟩ₖ = c ‘ j := by
  rw [indexedMarkerNames, value_definableGraph _ _ _ (markerIndexSet_marker hj)]
  simp [indexedMarkerValue, markerSymbol_not_mem_base]

theorem indexedMarkerNames_mem_function {B n c A : V} (hBA : B ⊆ A) (hc : c ∈ A ^ n) :
    indexedMarkerNames B n c ∈ A ^ markerIndexSet B n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  unfold indexedMarkerValue
  split_ifs with hiB
  · exact hBA i hiB
  · rcases mem_union_iff.mp hi with hb | hp
    · exact False.elim (hiB hb)
    · obtain ⟨b, hb, j, hj, rfl⟩ := mem_prod_iff.mp hp
      have hb' : b = B := by simpa using hb
      subst b
      simpa only [kpair.π₂_kpair] using function_value_mem hc hj

noncomputable def indexedMarkerStructure (B n A c : V) : V :=
  namedMembershipStructureCode (markerIndexSet B n) A (indexedMarkerNames B n c)

instance indexedMarkerStructure_definable : ℒₛₑₜ-function₄[V] indexedMarkerStructure := by
  unfold indexedMarkerStructure
  definability

@[simp] theorem indexedMarkerStructure_domain (B n A c : V) :
    structureDomain (indexedMarkerStructure B n A c) = A := namedMembershipStructureCode_domain _ _ _

theorem indexedMarkerStructure_expansion {B n A c : V} (hA : IsNonempty A)
    (hBA : B ⊆ A) (hc : c ∈ A ^ n) :
    IsMembershipExpansion (namedMembershipLanguageCode (markerIndexSet B n)) (indexedMarkerStructure B n A c) :=
  namedMembershipStructureCode_expansion hA (indexedMarkerNames_mem_function hBA hc)

theorem IsCodedElementaryEmbedding.indexedMarker_values {B n A C c d f : V} [IsTransitive B]
    (h : IsCodedElementaryEmbedding (namedMembershipLanguageCode (markerIndexSet B n))
      (indexedMarkerStructure B n A c) (indexedMarkerStructure B n C d) f)
    (hBA : B ⊆ A) (hc : c ∈ A ^ n) :
    (∀ j ∈ n, f ‘ (c ‘ j) = d ‘ j) ∧ ∀ i ∈ B, f ‘ i = i := by
  have hnames := indexedMarkerNames_mem_function hBA hc
  constructor
  · intro j hj
    simpa only [indexedMarkerNames_marker hj] using h.named_values hnames (markerIndexSet_marker hj)
  · intro i hi
    simpa only [indexedMarkerNames_base hi] using h.named_values hnames (markerIndexSet_base hi)

end ZFVP
