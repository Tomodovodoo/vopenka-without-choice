import ZFVP.SetTheory.DependentChoicePaths

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDependentChoicePathFormula : SetTheorySemisentence 5 :=
  “B κ A R f. !boundedFunctionFormula f κ A ∧ ∀ β ∈ κ,
    ∃ r ∈ B, !boundedFunctionFormula r β A ∧ !isSubsetOf r f ∧
      ∃ x ∈ A, !boundedPairMemberFormula f β x ∧ !boundedPairMemberFormula R r x”

theorem boundedDependentChoicePathFormula_bounded : IsBoundedSetFormula boundedDependentChoicePathFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 1) (.exs (.bvar 1)
    (.and (boundedFunctionFormula_bounded.subst _) (.and (isSubsetOf_bounded.subst _)
      (.exs (.bvar 4) (.and (boundedPairMemberFormula_bounded.subst _)
        (boundedPairMemberFormula_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsBoundedDependentChoicePath (B κ A R f : V) : Prop :=
  f ∈ A ^ κ ∧ ∀ β ∈ κ, ∃ r ∈ B, r ∈ A ^ β ∧ r ⊆ f ∧
    ∃ x ∈ A, ⟨β, x⟩ₖ ∈ f ∧ ⟨r, x⟩ₖ ∈ R

instance boundedDependentChoicePathFormula_defined :
    Defined (fun v : Fin 5 → V ↦ IsBoundedDependentChoicePath (v 0) (v 1) (v 2) (v 3) (v 4))
      boundedDependentChoicePathFormula :=
  ⟨fun v ↦ by simp [boundedDependentChoicePathFormula, IsBoundedDependentChoicePath]⟩

theorem boundedDependentChoicePath_iff {B κ A R f : V} [IsOrdinal κ]
    (hclosed : ∀ β ∈ κ, ∀ r ∈ A ^ β, r ∈ B) :
    IsBoundedDependentChoicePath B κ A R f ↔ IsDependentChoicePath A R κ f := by
  constructor
  · rintro ⟨hf, hsteps⟩
    let := IsFunction.of_mem hf
    refine ⟨hf, ?_⟩
    intro β hβ
    obtain ⟨r, _hrB, hr, hrsub, x, _hxA, hfx, hrx⟩ := hsteps β hβ
    have hrest := function_restrict_mem hf (IsOrdinal.toIsTransitive.transitive _ hβ)
    have hrsub' : r ⊆ f ↾ β := by
      intro z hz
      obtain ⟨i, hi, y, _hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hr z hz)
      exact kpair_mem_restrict_iff.mpr ⟨hrsub _ hz, hi⟩
    have he : r = f ↾ β := function_eq_of_subset hr hrest hrsub'
    have hx : f ‘ β = x := value_eq_of_kpair_mem hfx
    exact hx.symm ▸ he ▸ hrx
  · rintro ⟨hf, hsteps⟩
    let := IsFunction.of_mem hf
    refine ⟨hf, ?_⟩
    intro β hβ
    have hr := function_restrict_mem hf (IsOrdinal.toIsTransitive.transitive _ hβ)
    exact ⟨f ↾ β, hclosed β hβ _ hr, hr, restrict_subset _ _, f ‘ β,
      function_value_mem hf hβ,
      kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hβ), hsteps β hβ⟩

end ZFVP
