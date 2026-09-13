import ZFVP.ModelTheory.NamedMembershipEmbedding

/-! Membership with constants for a base set and one varying distinguished element. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def markerValue (B a i : V) : V := by
  classical
  exact if i = B then a else i

instance markerValue_definable : ℒₛₑₜ-function₃[V] markerValue := by
  have hd : ℒₛₑₜ-relation₄[V] (fun y B a i ↦ (i = B ∧ y = a) ∨ (i ≠ B ∧ y = i)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = markerValue (v 1) (v 2) (v 3) ↔ _
  unfold markerValue
  split_ifs <;> simp_all

noncomputable def markerNames (B a : V) : V :=
  definableGraph (succ B) (markerValue B a) (by definability)

instance markerNames_definable : ℒₛₑₜ-function₂[V] markerNames := by
  have hd : ℒₛₑₜ-relation₃[V] (fun F B a ↦ ∀ p,
      p ∈ F ↔ ∃ i ∈ succ B, p = ⟨i, markerValue B a i⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = markerNames (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [markerNames, mem_definableGraph_iff]

@[simp] theorem markerNames_marker (B a : V) : (markerNames B a) ‘ B = a := by
  rw [markerNames, value_definableGraph _ _ _ (by simp)]
  simp [markerValue]

theorem markerNames_base {B a i : V} (hi : i ∈ B) : (markerNames B a) ‘ i = i := by
  have hne : i ≠ B := fun he ↦ mem_irrefl B (he ▸ hi)
  rw [markerNames, value_definableGraph _ _ _ (by simp [mem_succ_iff, hi])]
  simp [markerValue, hne]

theorem markerNames_mem_function {B A a : V} (hBA : B ⊆ A) (ha : a ∈ A) :
    markerNames B a ∈ A ^ succ B := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  simp only [markerValue]
  split_ifs with he
  · exact ha
  · exact hBA i (by simpa [mem_succ_iff, he] using hi)

noncomputable def markerStructure (B A a : V) : V :=
  namedMembershipStructureCode (succ B) A (markerNames B a)

instance markerStructure_definable : ℒₛₑₜ-function₃[V] markerStructure := by
  unfold markerStructure
  definability

@[simp] theorem markerStructure_domain (B A a : V) :
    structureDomain (markerStructure B A a) = A := namedMembershipStructureCode_domain _ _ _

theorem markerStructure_expansion {B A a : V} (hA : IsNonempty A)
    (hBA : B ⊆ A) (ha : a ∈ A) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ B)) (markerStructure B A a) :=
  namedMembershipStructureCode_expansion hA (markerNames_mem_function hBA ha)

theorem IsCodedElementaryEmbedding.marker_values {B A C a b f : V}
    (h : IsCodedElementaryEmbedding (namedMembershipLanguageCode (succ B))
      (markerStructure B A a) (markerStructure B C b) f)
    (hBA : B ⊆ A) (ha : a ∈ A) : f ‘ a = b ∧ ∀ i ∈ B, f ‘ i = i := by
  have hc := markerNames_mem_function hBA ha
  refine ⟨?_, ?_⟩
  · simpa only [markerNames_marker] using h.named_values hc (show B ∈ succ B by simp)
  · intro i hi
    simpa only [markerNames_base hi] using
      h.named_values hc (show i ∈ succ B by simp [mem_succ_iff, hi])

end ZFVP
