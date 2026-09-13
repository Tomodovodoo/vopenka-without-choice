import ZFVP.SetTheory.OrdinalDependentChoice

/-! Equivalence with the nonempty-valued function formulation of
ordinal dependent choice in Spoerl, Definition 38. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalFunctionDependentChoiceAt (γ : V) : Prop :=
  ∀ A F : V, IsNonempty A → F ∈ (℘ A \ {∅}) ^ shorterSequences γ A →
    ∃ f ∈ A ^ γ, ∀ β ∈ γ, f ‘ β ∈ F ‘ (f ↾ β)

theorem functionDependentChoiceAt_of_relational {γ : V}
    (hDC : InternalDependentChoiceAt γ) : InternalFunctionDependentChoiceAt γ := by
  intro A F hA hF
  let R : V := {z ∈ shorterSequences γ A ×ˢ A ; kpair.π₂ z ∈ F ‘ (kpair.π₁ z)}
  have hR (s x : V) : ⟨s, x⟩ₖ ∈ R ↔
      s ∈ shorterSequences γ A ∧ x ∈ A ∧ x ∈ F ‘ s := by
    simp only [R, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    have hh : F ‘ s ⊆ A ∧ IsNonempty (F ‘ s) := by
      simpa using function_value_mem hF hs
    obtain ⟨x, hx⟩ := hh.2
    exact ⟨x, hh.1 x hx, (hR s x).mpr ⟨hs, hh.1 x hx, hx⟩⟩
  obtain ⟨f, hf, hstep⟩ := hDC A R hA hserial
  exact ⟨f, hf, fun β hβ ↦ ((hR _ _).mp (hstep β hβ)).2.2⟩

theorem relationalDependentChoiceAt_of_function {γ : V} [IsOrdinal γ]
    (hDC : InternalFunctionDependentChoiceAt γ) : InternalDependentChoiceAt γ := by
  intro A R hA hR
  let C : V → V := fun s ↦ {x ∈ A ; ⟨s, x⟩ₖ ∈ R}
  have hC : ℒₛₑₜ-function₁ C := by
    have h : ℒₛₑₜ-relation (fun B s : V ↦ ∀ x, x ∈ B ↔ x ∈ A ∧ ⟨s, x⟩ₖ ∈ R) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [C, mem_sep_iff]
    rfl
  let F := definableGraph (shorterSequences γ A) C hC
  have hF : F ∈ (℘ A \ {∅}) ^ shorterSequences γ A :=
    definableGraph_mem_function_of_mapsTo _ _ C hC (by
      intro s hs
      obtain ⟨x, hx, hsx⟩ := hR s hs
      have hh : C s ⊆ A ∧ IsNonempty (C s) :=
        ⟨fun _ hy ↦ (mem_sep_iff.mp hy).1, ⟨x, mem_sep_iff.mpr ⟨hx, hsx⟩⟩⟩
      simpa using hh)
  obtain ⟨f, hf, hstep⟩ := hDC A F hA hF
  refine ⟨f, hf, ?_⟩
  intro β hβ
  have hp : f ↾ β ∈ shorterSequences γ A := (mem_shorterSequences _ _ _).mpr
    ⟨β, hβ, function_restrict_mem hf (IsOrdinal.toIsTransitive.transitive _ hβ)⟩
  have hh := hstep β hβ
  rw [show F ‘ (f ↾ β) = C (f ↾ β) from value_definableGraph _ _ _ hp] at hh
  exact (mem_sep_iff.mp hh).2

theorem dependentChoiceAt_iff_function (γ : V) [IsOrdinal γ] :
    InternalDependentChoiceAt γ ↔ InternalFunctionDependentChoiceAt γ :=
  ⟨functionDependentChoiceAt_of_relational, relationalDependentChoiceAt_of_function⟩

end ZFVP
