import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.FiniteSequences
import ZFVP.SetTheory.DeltaOneBoundedTruth

/-! Dependent choices of an internal ordinal length. Serial relations
on shorter sequences represent the nonempty-valued functions in
Spoerl, Definition 38. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def shorterSequencesFormula : SetTheorySemisentence 3 :=
  f“S γ A. ∀ s, s ∈ S ↔ ∃ β ∈ γ, s ∈ !function.dfn A β”

def dependentChoiceAtFormula : SetTheorySemisentence 1 :=
  f“γ. ∀ A R, !boundedNonemptyFormula A →
    (∀ s ∈ !shorterSequencesFormula γ A, ∃ x ∈ A, !kpair.dfn s x ∈ R) →
    ∃ f ∈ !function.dfn A γ, ∀ β ∈ γ,
      !kpair.dfn (!restrict.dfn f β) (!value.dfn f β) ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def shorterSequences (γ A : V) : V :=
  ⋃ˢ repl (fun β ↦ A ^ β) (by definability) γ

theorem mem_shorterSequences (γ A s : V) :
    s ∈ shorterSequences γ A ↔ ∃ β ∈ γ, s ∈ A ^ β := by
  simp only [shorterSequences, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨B, ⟨β, hβ, rfl⟩, hs⟩
    exact ⟨β, hβ, hs⟩
  · rintro ⟨β, hβ, hs⟩
    exact ⟨A ^ β, ⟨β, hβ, rfl⟩, hs⟩

instance shorterSequencesFormula_defined :
    ℒₛₑₜ-function₂[V] shorterSequences via shorterSequencesFormula :=
  ⟨fun v ↦ by
    simp [shorterSequencesFormula]
    rw [mem_ext_iff]
    simp only [mem_shorterSequences]⟩

instance shorterSequences_definable : ℒₛₑₜ-function₂[V] shorterSequences :=
  shorterSequencesFormula_defined.to_definable

theorem mem_shorterSequences_domain (γ A s : V) :
    s ∈ shorterSequences γ A ↔ domain s ∈ γ ∧ s ∈ A ^ domain s := by
  rw [mem_shorterSequences]
  constructor
  · rintro ⟨β, hβ, hs⟩
    rw [domain_eq_of_mem_function hs]
    exact ⟨hβ, hs⟩
  · rintro ⟨hβ, hs⟩
    exact ⟨domain s, hβ, hs⟩

def InternalDependentChoiceAt (γ : V) : Prop :=
  ∀ A R : V, IsNonempty A →
    (∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) →
    ∃ f ∈ A ^ γ, ∀ β ∈ γ, ⟨f ↾ β, f ‘ β⟩ₖ ∈ R

instance dependentChoiceAtFormula_defined :
    ℒₛₑₜ-predicate[V] InternalDependentChoiceAt via dependentChoiceAtFormula :=
  ⟨fun v ↦ by simp [dependentChoiceAtFormula, InternalDependentChoiceAt]⟩

instance dependentChoiceAt_definable : ℒₛₑₜ-predicate[V] InternalDependentChoiceAt :=
  dependentChoiceAtFormula_defined.to_definable

theorem dependentChoiceAt_zero : InternalDependentChoiceAt (0 : V) := by
  intro A R _ _
  refine ⟨∅, ?_, ?_⟩
  · simp [mem_function_iff, zero_def]
  · simp [zero_def]

theorem InternalDependentChoiceAt.downward {α γ : V} [IsOrdinal α] [IsOrdinal γ]
    (hγ : InternalDependentChoiceAt γ) (hαγ : α ⊆ γ) : InternalDependentChoiceAt α := by
  intro A R hA hR
  let Q : V := {z ∈ shorterSequences γ A ×ˢ A ;
    domain (kpair.π₁ z) ∈ α → z ∈ R}
  have hQ (s x : V) : ⟨s, x⟩ₖ ∈ Q ↔
      s ∈ shorterSequences γ A ∧ x ∈ A ∧ (domain s ∈ α → ⟨s, x⟩ₖ ∈ R) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ Q := by
    intro s hs
    by_cases hd : domain s ∈ α
    · obtain ⟨x, hx, hsx⟩ := hR s ((mem_shorterSequences_domain _ _ _).mpr
        ⟨hd, ((mem_shorterSequences_domain _ _ _).mp hs).2⟩)
      exact ⟨x, hx, (hQ s x).mpr ⟨hs, hx, fun _ ↦ hsx⟩⟩
    · obtain ⟨x, hx⟩ := hA
      exact ⟨x, hx, (hQ s x).mpr ⟨hs, hx, fun h ↦ False.elim (hd h)⟩⟩
  obtain ⟨f, hf, hstep⟩ := hγ A Q hA hserial
  let := IsFunction.of_mem hf
  refine ⟨f ↾ α, function_restrict_mem hf hαγ, ?_⟩
  intro β hβ
  have hβγ := hαγ β hβ
  have hsub : β ⊆ α := IsOrdinal.toIsTransitive.transitive _ hβ
  have hfβ := function_restrict_mem hf (subset_trans hsub hαγ)
  have hs := ((hQ _ _).mp (hstep β hβγ)).2.2
    (by rw [domain_eq_of_mem_function hfβ]; exact hβ)
  rw [restrict_restrict_of_subset hsub,
    value_restrict (by rw [domain_eq_of_mem_function hf]; exact hβγ) hβ]
  exact hs

end ZFVP
