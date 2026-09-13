import ZFVP.ModelTheory.InternalCodedProofSupport
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.FinitePartialFunctions

/-! Countable internal membership theories and their finite consistent extensions.
All sets and proof quantifiers here are internal to the ambient ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def countableCodedOpenTheoryFormula : SetTheorySemisentence 1 :=
  f“T. !internallyCountableFormula T ∧
    ∀ a ∈ T, a ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty)”

def finiteConsistentOpenExtensionFormula : SetTheorySemisentence 3 :=
  f“T A Γ. (∀ a ∈ Γ, a ∈ A) ∧ !internallyFiniteFormula Γ ∧
    !openCodedSequentConsistentFormula (!union.dfn T Γ)”

def finiteConsistentOpenExtensionsFormula : SetTheorySemisentence 3 :=
  f“P T A. ∀ Γ, Γ ∈ P ↔ !finiteConsistentOpenExtensionFormula T A Γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCountableCodedOpenTheory (T : V) : Prop :=
  IsInternallyCountable T ∧ T ⊆ formulaFamily membershipLanguageCode ∅

instance countableCodedOpenTheoryFormula_defined :
    ℒₛₑₜ-predicate[V] IsCountableCodedOpenTheory via countableCodedOpenTheoryFormula :=
  ⟨fun v ↦ by simp [countableCodedOpenTheoryFormula, IsCountableCodedOpenTheory, subset_def]⟩

instance countableCodedOpenTheory_definable : ℒₛₑₜ-predicate[V] IsCountableCodedOpenTheory :=
  countableCodedOpenTheoryFormula_defined.to_definable

theorem IsCountableCodedOpenTheory.subtheory {T U : V} (hU : IsCountableCodedOpenTheory U)
    (hTU : T ⊆ U) : IsCountableCodedOpenTheory T :=
  ⟨internallyCountable_subset hU.1 hTU, subset_trans hTU hU.2⟩

theorem IsCountableCodedOpenTheory.union {T U : V} (hT : IsCountableCodedOpenTheory T)
    (hU : IsCountableCodedOpenTheory U) : IsCountableCodedOpenTheory (T ∪ U) :=
  ⟨internallyCountable_union hT.1 hU.1,
    fun _ ha ↦ (mem_union_iff.mp ha).elim (hT.2 _) (hU.2 _)⟩

theorem IsCountableCodedOpenTheory.extend_finite {T A Γ : V} (hT : IsCountableCodedOpenTheory T)
    (hA : A ⊆ formulaFamily membershipLanguageCode ∅) (hΓ : Γ ⊆ A)
    (hfin : IsInternallyFinite Γ) : IsCountableCodedOpenTheory (T ∪ Γ) :=
  hT.union ⟨internallyCountable_of_finite hfin, subset_trans hΓ hA⟩

def IsFiniteConsistentOpenExtension (T A Γ : V) : Prop :=
  Γ ⊆ A ∧ IsInternallyFinite Γ ∧ OpenCodedSequentConsistent (T ∪ Γ)

instance finiteConsistentOpenExtensionFormula_defined :
    ℒₛₑₜ-relation₃[V] IsFiniteConsistentOpenExtension via finiteConsistentOpenExtensionFormula :=
  ⟨fun v ↦ by simp [finiteConsistentOpenExtensionFormula, IsFiniteConsistentOpenExtension, subset_def]⟩

instance finiteConsistentOpenExtension_definable :
    ℒₛₑₜ-relation₃[V] IsFiniteConsistentOpenExtension :=
  finiteConsistentOpenExtensionFormula_defined.to_definable

noncomputable def finiteConsistentOpenExtensions (T A : V) : V :=
  {Γ ∈ ℘ A ; IsInternallyFinite Γ ∧ OpenCodedSequentConsistent (T ∪ Γ)}

theorem mem_finiteConsistentOpenExtensions_iff (T A Γ : V) :
    Γ ∈ finiteConsistentOpenExtensions T A ↔ IsFiniteConsistentOpenExtension T A Γ := by
  simp only [finiteConsistentOpenExtensions, mem_sep_iff, mem_power_iff,
    IsFiniteConsistentOpenExtension]

instance finiteConsistentOpenExtensionsFormula_defined :
    ℒₛₑₜ-function₂[V] finiteConsistentOpenExtensions via finiteConsistentOpenExtensionsFormula :=
  ⟨fun v ↦ by
    change finiteConsistentOpenExtensionsFormula.Evalb v ↔
      v 0 = finiteConsistentOpenExtensions (v 1) (v 2)
    simp only [finiteConsistentOpenExtensionsFormula, mem_ext_iff,
      mem_finiteConsistentOpenExtensions_iff]
    simp⟩

instance finiteConsistentOpenExtensions_definable :
    ℒₛₑₜ-function₂[V] finiteConsistentOpenExtensions :=
  finiteConsistentOpenExtensionsFormula_defined.to_definable

theorem empty_mem_finiteConsistentOpenExtensions_iff (T A : V) :
    (∅ : V) ∈ finiteConsistentOpenExtensions T A ↔ OpenCodedSequentConsistent T := by
  rw [mem_finiteConsistentOpenExtensions_iff]
  simp only [IsFiniteConsistentOpenExtension, empty_subset, true_and, union_empty]
  exact and_iff_right internallyFinite_empty

theorem finiteConsistentOpenExtensions_subset {T A Γ Δ : V}
    (hΓ : Γ ∈ finiteConsistentOpenExtensions T A) (hΔ : Δ ⊆ Γ) :
    Δ ∈ finiteConsistentOpenExtensions T A := by
  obtain ⟨hA, hfin, hcon⟩ := (mem_finiteConsistentOpenExtensions_iff T A Γ).mp hΓ
  refine (mem_finiteConsistentOpenExtensions_iff T A Δ).mpr
    ⟨subset_trans hΔ hA, internallyFinite_subset hfin hΔ, hcon.subtheory ?_⟩
  intro x hx
  exact (mem_union_iff.mp hx).elim (fun h ↦ mem_union_iff.mpr (Or.inl h))
    (fun h ↦ mem_union_iff.mpr (Or.inr (hΔ _ h)))

theorem finiteConsistentOpenExtensions_poset (T A : V) :
    IsForcingPoset (finiteConsistentOpenExtensions T A)
      (reverseInclusionOrder (finiteConsistentOpenExtensions T A)) := reverseInclusionOrder_poset _

theorem finiteConsistentOpenExtensions_top {T A : V} (hT : OpenCodedSequentConsistent T) :
    IsForcingTop (finiteConsistentOpenExtensions T A)
      (reverseInclusionOrder (finiteConsistentOpenExtensions T A)) ∅ := by
  have he := (empty_mem_finiteConsistentOpenExtensions_iff T A).mpr hT
  exact ⟨he, fun Γ hΓ ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hΓ, he, empty_subset _⟩⟩

/-- Compatibility is exactly consistency of adjoining both finite conditions.
No decision or Henkin density assertion is built into this characterization. -/
theorem finiteConsistentOpenExtensions_compatible_iff {T A Γ Δ : V}
    (hΓ : Γ ∈ finiteConsistentOpenExtensions T A) (hΔ : Δ ∈ finiteConsistentOpenExtensions T A) :
    ForcingCompatible (finiteConsistentOpenExtensions T A)
      (reverseInclusionOrder (finiteConsistentOpenExtensions T A)) Γ Δ ↔
        OpenCodedSequentConsistent (T ∪ (Γ ∪ Δ)) := by
  constructor
  · rintro ⟨Ξ, hΞ, hΞΓ, hΞΔ⟩
    have hc := ((mem_finiteConsistentOpenExtensions_iff T A Ξ).mp hΞ).2.2
    apply hc.subtheory
    intro x hx
    rcases mem_union_iff.mp hx with h | h
    · exact mem_union_iff.mpr (Or.inl h)
    · apply mem_union_iff.mpr ∘ Or.inr
      exact (mem_union_iff.mp h).elim
        (((pair_mem_reverseInclusionOrder _ _ _).mp hΞΓ).2.2 x)
        (((pair_mem_reverseInclusionOrder _ _ _).mp hΞΔ).2.2 x)
  · intro hcon
    obtain ⟨hΓA, hΓfin, _⟩ := (mem_finiteConsistentOpenExtensions_iff T A Γ).mp hΓ
    obtain ⟨hΔA, hΔfin, _⟩ := (mem_finiteConsistentOpenExtensions_iff T A Δ).mp hΔ
    have hu : Γ ∪ Δ ∈ finiteConsistentOpenExtensions T A :=
      (mem_finiteConsistentOpenExtensions_iff T A _).mpr
        ⟨fun _ hx ↦ (mem_union_iff.mp hx).elim (hΓA _) (hΔA _),
          internallyFinite_union hΓfin hΔfin, hcon⟩
    exact ⟨Γ ∪ Δ, hu,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hΓ, fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hΔ, fun _ hx ↦ mem_union_iff.mpr (Or.inr hx)⟩⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_countableCodedOpenTheory_iff (j : ElementaryMap V W) (T : V) :
    IsCountableCodedOpenTheory (j T) ↔ IsCountableCodedOpenTheory T :=
  (j.map_defined countableCodedOpenTheoryFormula
    (fun v ↦ IsCountableCodedOpenTheory (v 0))
    (fun v ↦ IsCountableCodedOpenTheory (v 0)) ![T]).symm

theorem map_finiteConsistentOpenExtension_iff (j : ElementaryMap V W) (T A Γ : V) :
    IsFiniteConsistentOpenExtension (j T) (j A) (j Γ) ↔ IsFiniteConsistentOpenExtension T A Γ :=
  (j.map_defined finiteConsistentOpenExtensionFormula
    (fun v ↦ IsFiniteConsistentOpenExtension (v 0) (v 1) (v 2))
    (fun v ↦ IsFiniteConsistentOpenExtension (v 0) (v 1) (v 2)) ![T, A, Γ]).symm

theorem map_finiteConsistentOpenExtensions (j : ElementaryMap V W) (T A : V) :
    j (finiteConsistentOpenExtensions T A) = finiteConsistentOpenExtensions (j T) (j A) :=
  (j.map_defined finiteConsistentOpenExtensionsFormula
    (fun v ↦ v 0 = finiteConsistentOpenExtensions (v 1) (v 2))
    (fun v ↦ v 0 = finiteConsistentOpenExtensions (v 1) (v 2))
      ![finiteConsistentOpenExtensions T A, T, A]).mp rfl

end ElementaryMap

end ZFVP
