import ZFVP.SetTheory.OrdinalDependentChoice
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def dependentChoicePathFormula : SetTheorySemisentence 4 :=
  f“A R α s. s ∈ !function.dfn A α ∧ ∀ β ∈ α,
    !kpair.dfn (!restrict.dfn s β) (!value.dfn s β) ∈ R”

def dependentChoicePathsFormula : SetTheorySemisentence 4 :=
  f“B κ A R. ∀ s, s ∈ B ↔ s ∈ !shorterSequencesFormula κ A ∧
    !dependentChoicePathFormula A R (!domain.dfn s) s”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsDependentChoicePath (A R α s : V) : Prop :=
  s ∈ A ^ α ∧ ∀ β ∈ α, ⟨s ↾ β, s ‘ β⟩ₖ ∈ R

instance dependentChoicePathFormula_defined :
    ℒₛₑₜ-relation₄[V] IsDependentChoicePath via dependentChoicePathFormula :=
  ⟨fun v ↦ by simp [dependentChoicePathFormula, IsDependentChoicePath]⟩

instance dependentChoicePath_definable : ℒₛₑₜ-relation₄[V] IsDependentChoicePath := by
  unfold IsDependentChoicePath
  definability

noncomputable def dependentChoicePaths (κ A R : V) : V :=
  {s ∈ shorterSequences κ A ; IsDependentChoicePath A R (domain s) s}

instance dependentChoicePathsFormula_defined :
    ℒₛₑₜ-function₃[V] dependentChoicePaths via dependentChoicePathsFormula :=
  ⟨fun v ↦ by
    simp [dependentChoicePathsFormula]
    rw [mem_ext_iff]
    simp only [dependentChoicePaths, mem_sep_iff]⟩

instance dependentChoicePaths_definable : ℒₛₑₜ-function₃[V] dependentChoicePaths :=
  dependentChoicePathsFormula_defined.to_definable

theorem mem_dependentChoicePaths (κ A R s : V) :
    s ∈ dependentChoicePaths κ A R ↔
      domain s ∈ κ ∧ IsDependentChoicePath A R (domain s) s := by
  simp only [dependentChoicePaths, mem_sep_iff, mem_shorterSequences_domain,
    IsDependentChoicePath]
  tauto

theorem dependentChoicePath_empty (A R : V) : IsDependentChoicePath A R ∅ ∅ := by
  constructor
  · simp [mem_function_iff]
  · simp

theorem IsDependentChoicePath.restrict {A R α β s : V} [IsOrdinal α] [IsOrdinal β]
    (hs : IsDependentChoicePath A R α s) (hβ : β ⊆ α) :
    IsDependentChoicePath A R β (s ↾ β) := by
  let := IsFunction.of_mem hs.1
  refine ⟨function_restrict_mem hs.1 hβ, ?_⟩
  intro ξ hξ
  have hξα := hβ ξ hξ
  have hξβ : ξ ⊆ β := by
    exact IsOrdinal.toIsTransitive.transitive _ hξ
  rw [restrict_restrict_of_subset hξβ,
    value_restrict (by rw [domain_eq_of_mem_function hs.1]; exact hξα) hξ]
  exact hs.2 ξ hξα

theorem dependentChoicePath_extend {κ α β A R s : V}
    [IsOrdinal κ] [IsOrdinal α] [IsOrdinal β]
    (hDC : InternalDependentChoiceAt α) (hακ : α ⊆ κ) (hβα : β ⊆ α)
    (hA : IsNonempty A)
    (hR : ∀ u ∈ shorterSequences κ A, ∃ x ∈ A, ⟨u, x⟩ₖ ∈ R)
    (hs : IsDependentChoicePath A R β s) :
    ∃ t, IsDependentChoicePath A R α t ∧ s ⊆ t := by
  let := IsFunction.of_mem hs.1
  let Q : V := {z ∈ shorterSequences α A ×ˢ A ;
    (domain (kpair.π₁ z) ∈ β → kpair.π₂ z = s ‘ (domain (kpair.π₁ z))) ∧
    (domain (kpair.π₁ z) ∉ β → z ∈ R)}
  have hQ (u x : V) : ⟨u, x⟩ₖ ∈ Q ↔ u ∈ shorterSequences α A ∧ x ∈ A ∧
      (domain u ∈ β → x = s ‘ (domain u)) ∧ (domain u ∉ β → ⟨u, x⟩ₖ ∈ R) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ u ∈ shorterSequences α A, ∃ x ∈ A, ⟨u, x⟩ₖ ∈ Q := by
    intro u hu
    by_cases hd : domain u ∈ β
    · have hx := function_value_mem hs.1 hd
      exact ⟨s ‘ (domain u), hx, (hQ _ _).mpr ⟨hu, hx, fun _ ↦ rfl, fun hn ↦ False.elim (hn hd)⟩⟩
    · obtain ⟨ξ, hξ, huf⟩ := (mem_shorterSequences _ _ _).mp hu
      obtain ⟨x, hx, hux⟩ := hR u ((mem_shorterSequences _ _ _).mpr ⟨ξ, hακ ξ hξ, huf⟩)
      exact ⟨x, hx, (hQ _ _).mpr ⟨hu, hx, fun hh ↦ False.elim (hd hh), fun _ ↦ hux⟩⟩
  obtain ⟨t, ht, hstep⟩ := hDC A Q hA hserial
  let := IsFunction.of_mem ht
  have hdom (ξ : V) (hξ : ξ ∈ α) : domain (t ↾ ξ) = ξ :=
    domain_eq_of_mem_function (function_restrict_mem ht (IsOrdinal.toIsTransitive.transitive _ hξ))
  have hval (ξ : V) (hξ : ξ ∈ β) : t ‘ ξ = s ‘ ξ := by
    have hh := ((hQ _ _).mp (hstep ξ (hβα ξ hξ))).2.2.1
    rw [hdom ξ (hβα ξ hξ)] at hh
    exact hh hξ
  have hrestrict : t ↾ β = s := by
    have hh := restrict_eq_of_values (f := t) (g := s) (A := β)
      (by rw [domain_eq_of_mem_function ht]; exact hβα)
      (by rw [domain_eq_of_mem_function hs.1]) hval
    simpa only [IsFunction.restrict_eq_self s β (by rw [domain_eq_of_mem_function hs.1])] using hh
  refine ⟨t, ⟨ht, ?_⟩, ?_⟩
  · intro ξ hξ
    by_cases hξβ : ξ ∈ β
    · have hh := hs.2 ξ hξβ
      rw [← hrestrict, restrict_restrict_of_subset (IsOrdinal.toIsTransitive.transitive _ hξβ)] at hh
      rwa [value_restrict (by rw [domain_eq_of_mem_function ht]; exact hξ) hξβ] at hh
    · have hh := ((hQ _ _).mp (hstep ξ hξ)).2.2.2
      rw [hdom ξ hξ] at hh
      exact hh hξβ
  · rw [← hrestrict]
    exact restrict_subset _ _

end ZFVP
