import ZFVP.ModelTheory.NamedMembershipEmbedding

/-! A fixed membership language naming a base set and two varying parameters. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def twoMarkerValue (B a X i : V) : V := by
  classical
  exact if i = B then a else if i = succ B then X else i

instance twoMarkerValue_definable : ℒₛₑₜ-function₄[V] twoMarkerValue := by
  have hd : ℒₛₑₜ-relation₅[V] (fun y B a X i ↦
      (i = B ∧ y = a) ∨ (i ≠ B ∧ i = succ B ∧ y = X) ∨
        (i ≠ B ∧ i ≠ succ B ∧ y = i)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = twoMarkerValue (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold twoMarkerValue
  split_ifs <;> simp_all

noncomputable def twoMarkerNames (B a X : V) : V :=
  definableGraph (succ (succ B)) (twoMarkerValue B a X) (by definability)

instance twoMarkerNames_definable : ℒₛₑₜ-function₃[V] twoMarkerNames := by
  have hd : ℒₛₑₜ-relation₄[V] (fun F B a X ↦ ∀ p,
      p ∈ F ↔ ∃ i ∈ succ (succ B), p = ⟨i, twoMarkerValue B a X i⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = twoMarkerNames (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [twoMarkerNames, mem_definableGraph_iff]

@[simp] theorem twoMarkerNames_first (B a X : V) : (twoMarkerNames B a X) ‘ B = a := by
  rw [twoMarkerNames, value_definableGraph _ _ _ (by simp [mem_succ_iff])]
  simp [twoMarkerValue]

@[simp] theorem twoMarkerNames_second (B a X : V) : (twoMarkerNames B a X) ‘ (succ B) = X := by
  have hne : succ B ≠ B := by
    intro he
    have hm : B ∈ succ B := by simp
    rw [he] at hm
    exact mem_irrefl B hm
  rw [twoMarkerNames, value_definableGraph _ _ _ (by simp)]
  simp [twoMarkerValue, hne]

theorem twoMarkerNames_base {B a X i : V} (hi : i ∈ B) : (twoMarkerNames B a X) ‘ i = i := by
  have hne : i ≠ B := fun he ↦ mem_irrefl B (he ▸ hi)
  have hne' : i ≠ succ B := by
    intro he
    have hm : succ B ∈ B := he ▸ hi
    exact mem_asymm hm (by simp)
  rw [twoMarkerNames, value_definableGraph _ _ _ (by simp [mem_succ_iff, hi])]
  simp [twoMarkerValue, hne, hne']

theorem twoMarkerNames_mem_function {B A a X : V} (hBA : B ⊆ A) (ha : a ∈ A) (hX : X ∈ A) :
    twoMarkerNames B a X ∈ A ^ succ (succ B) := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  simp only [twoMarkerValue]
  split_ifs with h₁ h₂
  · exact ha
  · exact hX
  · exact hBA i (by simpa [mem_succ_iff, h₁, h₂] using hi)

noncomputable def twoMarkerStructure (B A a X : V) : V :=
  namedMembershipStructureCode (succ (succ B)) A (twoMarkerNames B a X)

instance twoMarkerStructure_definable : ℒₛₑₜ-function₄[V] twoMarkerStructure := by
  unfold twoMarkerStructure
  definability

@[simp] theorem twoMarkerStructure_domain (B A a X : V) :
    structureDomain (twoMarkerStructure B A a X) = A := namedMembershipStructureCode_domain _ _ _

theorem twoMarkerStructure_valid {B A a X : V} (hA : IsNonempty A)
    (hBA : B ⊆ A) (ha : a ∈ A) (hX : X ∈ A) :
    IsStructureCode (namedMembershipLanguageCode (succ (succ B))) (twoMarkerStructure B A a X) :=
  namedMembershipStructureCode_valid hA (twoMarkerNames_mem_function hBA ha hX)

theorem twoMarkerStructure_expansion {B A a X : V} (hA : IsNonempty A)
    (hBA : B ⊆ A) (ha : a ∈ A) (hX : X ∈ A) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ (succ B))) (twoMarkerStructure B A a X) :=
  namedMembershipStructureCode_expansion hA (twoMarkerNames_mem_function hBA ha hX)

theorem IsCodedElementaryEmbedding.twoMarker_values {B A C a b X Y f : V}
    (h : IsCodedElementaryEmbedding (namedMembershipLanguageCode (succ (succ B)))
      (twoMarkerStructure B A a X) (twoMarkerStructure B C b Y) f)
    (hBA : B ⊆ A) (ha : a ∈ A) (hX : X ∈ A) :
    f ‘ a = b ∧ f ‘ X = Y ∧ ∀ i ∈ B, f ‘ i = i := by
  have hc := twoMarkerNames_mem_function hBA ha hX
  refine ⟨?_, ?_, ?_⟩
  · simpa only [twoMarkerNames_first] using h.named_values hc (show B ∈ succ (succ B) by simp [mem_succ_iff])
  · simpa only [twoMarkerNames_second] using h.named_values hc (show succ B ∈ succ (succ B) by simp)
  · intro i hi
    simpa only [twoMarkerNames_base hi] using h.named_values hc (show i ∈ succ (succ B) by simp [mem_succ_iff, hi])

end ZFVP
