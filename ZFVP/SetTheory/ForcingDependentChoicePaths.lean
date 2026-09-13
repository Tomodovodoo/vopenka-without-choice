import ZFVP.SetTheory.DependentChoiceSerialPaths
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.FunctionMap
import ZFVP.SetTheory.FormulaForcing
import ZFVP.Syntax.StandardTuples

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def dependentChoiceSerialFormula : SetTheorySemisentence 3 :=
  f“γ A B. !boundedNonemptyFormula A ∧
    ∀ s ∈ !shorterSequencesFormula γ A, ∃ x ∈ A, !kpair.dfn s x ∈ B”

def dependentChoiceBranchFormula : SetTheorySemisentence 3 :=
  f“γ A B. ∃ s, !dependentChoicePathFormula A B γ s”

def dependentChoiceNextFormula : SetTheorySemisentence 4 :=
  f“s x A B. x ∈ A ∧ !kpair.dfn s x ∈ B”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_dependentChoiceSerialFormula (v : Fin 3 → V) :
    dependentChoiceSerialFormula.Evalb v ↔ IsNonempty (v 1) ∧
      ∀ s ∈ shorterSequences (v 0) (v 1), ∃ x ∈ v 1, ⟨s, x⟩ₖ ∈ v 2 := by
  simp [dependentChoiceSerialFormula]

theorem eval_dependentChoiceBranchFormula (v : Fin 3 → V) :
    dependentChoiceBranchFormula.Evalb v ↔ ∃ s, IsDependentChoicePath (v 1) (v 2) (v 0) s := by
  simp [dependentChoiceBranchFormula]

theorem eval_dependentChoiceNextFormula (v : Fin 4 → V) :
    dependentChoiceNextFormula.Evalb v ↔ v 1 ∈ v 2 ∧ ⟨v 0, v 1⟩ₖ ∈ v 3 := by
  simp [dependentChoiceNextFormula]

noncomputable def conditionSequence (s : V) : V := functionMap kpair.π₁ (by definability) s
noncomputable def subnameSequence (s : V) : V := functionMap kpair.π₂ (by definability) s

instance conditionSequence_definable : ℒₛₑₜ-function₁[V] conditionSequence :=
  functionMap_definable kpair.π₁ (by definability)
instance subnameSequence_definable : ℒₛₑₜ-function₁[V] subnameSequence :=
  functionMap_definable kpair.π₂ (by definability)

instance conditionSequence_isFunction (s : V) : IsFunction (conditionSequence s) :=
  functionMap_isFunction _ _ _
instance subnameSequence_isFunction (s : V) : IsFunction (subnameSequence s) :=
  functionMap_isFunction _ _ _

theorem conditionSequence_domain (s : V) : domain (conditionSequence s) = domain s := functionMap_domain _ _ _
theorem subnameSequence_domain (s : V) : domain (subnameSequence s) = domain s := functionMap_domain _ _ _

theorem conditionSequence_value {s i : V} (hi : i ∈ domain s) :
    (conditionSequence s) ‘ i = kpair.π₁ (s ‘ i) := functionMap_value _ _ hi
theorem subnameSequence_value {s i : V} (hi : i ∈ domain s) :
    (subnameSequence s) ‘ i = kpair.π₂ (s ‘ i) := functionMap_value _ _ hi

theorem conditionSequence_function {s α P N : V} (hs : s ∈ (P ×ˢ N) ^ α) :
    conditionSequence s ∈ P ^ α := functionMap_mem_function _ _ hs (by
  intro x hx
  obtain ⟨p, hp, σ, _, rfl⟩ := mem_prod_iff.mp hx
  simpa using hp)

theorem subnameSequence_function {s α P N : V} (hs : s ∈ (P ×ˢ N) ^ α) :
    subnameSequence s ∈ N ^ α := functionMap_mem_function _ _ hs (by
  intro x hx
  obtain ⟨p, _, σ, hσ, rfl⟩ := mem_prod_iff.mp hx
  simpa using hσ)

theorem subnameSequence_isNameSequence {P τ s α : V} (hτ : IsForcingName P τ)
    (hs : s ∈ (P ×ˢ domain τ) ^ α) : IsNameSequence P (subnameSequence s) := by
  have hf := subnameSequence_function hs
  intro i hi
  have hiα : i ∈ α := domain_eq_of_mem_function hf ▸ hi
  obtain ⟨p, hp⟩ := mem_domain_iff.mp (function_value_mem hf hiα)
  exact forcingName_subname hτ hp

theorem subnameSequence_restrict {s A : V} [IsFunction s] (hA : A ⊆ domain s) :
    subnameSequence (s ↾ A) = (subnameSequence s) ↾ A := functionMap_restrict _ _ hA

def ForcesDependentChoiceNext (P R one τA τB s q σ : V) : Prop :=
  q ∈ forcingFormula P R dependentChoiceNextFormula
    (standardTuple ![sequenceName one (subnameSequence s), σ, τA, τB])

instance forcesDependentChoiceNext_definable (P R one τA τB : V) :
    ℒₛₑₜ-relation₃[V] (ForcesDependentChoiceNext P R one τA τB) := by
  unfold ForcesDependentChoiceNext
  simp only [standardTuple]
  definability

noncomputable def dependentChoiceForcingRelation (P R one τA τB p γ : V) : V :=
  {z ∈ shorterSequences γ (P ×ˢ domain τA) ×ˢ (P ×ˢ domain τA) ;
    ⟨kpair.π₁ (kpair.π₂ z), p⟩ₖ ∈ R ∧
    (∀ i ∈ domain (kpair.π₁ z), ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ ((kpair.π₁ z) ‘ i)⟩ₖ ∈ R) ∧
    ForcesDependentChoiceNext P R one τA τB (kpair.π₁ z) (kpair.π₁ (kpair.π₂ z))
      (kpair.π₂ (kpair.π₂ z))}

theorem pair_mem_dependentChoiceForcingRelation (P R one τA τB p γ s z : V) :
    ⟨s, z⟩ₖ ∈ dependentChoiceForcingRelation P R one τA τB p γ ↔
      s ∈ shorterSequences γ (P ×ˢ domain τA) ∧ z ∈ P ×ˢ domain τA ∧
      ⟨kpair.π₁ z, p⟩ₖ ∈ R ∧
      (∀ i ∈ domain s, ⟨kpair.π₁ z, kpair.π₁ (s ‘ i)⟩ₖ ∈ R) ∧
      ForcesDependentChoiceNext P R one τA τB s (kpair.π₁ z) (kpair.π₂ z) := by
  simp only [dependentChoiceForcingRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem dependentChoiceForcingPath_bounds {P R one τA τB p γ α s : V} [IsOrdinal α]
    (hs : IsDependentChoicePath (P ×ˢ domain τA)
      (dependentChoiceForcingRelation P R one τA τB p γ) α s) :
    IsForcingDescending P R α (conditionSequence s) ∧
      ∀ i ∈ α, ⟨(conditionSequence s) ‘ i, p⟩ₖ ∈ R := by
  let := IsFunction.of_mem hs.1
  have hv (i : V) (hi : i ∈ α) : (conditionSequence s) ‘ i = kpair.π₁ (s ‘ i) :=
    conditionSequence_value (by rw [domain_eq_of_mem_function hs.1]; exact hi)
  have hstep (i : V) (hi : i ∈ α) :=
    (pair_mem_dependentChoiceForcingRelation P R one τA τB p γ _ _).mp (hs.2 i hi)
  refine ⟨⟨conditionSequence_function hs.1, ?_⟩, ?_⟩
  · intro i hi j hj
    have hjs := IsOrdinal.toIsTransitive.mem_trans hj hi
    have hsi := function_restrict_mem hs.1 (IsOrdinal.toIsTransitive.transitive _ hi)
    have hh := (hstep i hi).2.2.2.1 j (by rw [domain_eq_of_mem_function hsi]; exact hj)
    rw [value_restrict (by rw [domain_eq_of_mem_function hs.1]; exact hjs) hj] at hh
    simpa only [hv i hi, hv j hjs] using hh
  · intro i hi
    rw [hv i hi]
    exact (hstep i hi).2.2.1

end ZFVP
