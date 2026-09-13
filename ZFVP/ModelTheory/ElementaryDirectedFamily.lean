import ZFVP.ModelTheory.ElementaryParameterClosure

/-! Directedness and containment witnesses reflect to the intersection of an
internal family with an elementary submodel of a transitive set. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedFamilyUpperBoundFormula : SetTheorySemisentence 4 :=
  “Z F A C. Z ∈ F ∧ !isSubsetOf A Z ∧ !isSubsetOf C Z”

theorem boundedFamilyUpperBoundFormula_bounded : IsBoundedSetFormula boundedFamilyUpperBoundFormula :=
  .and (.rel _ _) (.and (isSubsetOf_bounded.subst _) (isSubsetOf_bounded.subst _))

def boundedFamilyContainmentFormula : SetTheorySemisentence 3 :=
  “Z F A. Z ∈ F ∧ !isSubsetOf A Z”

theorem boundedFamilyContainmentFormula_bounded : IsBoundedSetFormula boundedFamilyContainmentFormula :=
  .and (.rel _ _) (isSubsetOf_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {Y B F : V} (h : IsElementaryInclusion Y B) [IsTransitive B]

include h in
theorem containing_member (hF : F ∈ Y) {a : V} (ha : a ∈ Y)
    (hex : ∃ Z ∈ F, a ⊆ Z) : ∃ Z ∈ F ∩ Y, a ⊆ Z := by
  obtain ⟨Z, hZF, haZ⟩ := hex
  have hZB := (inferInstance : IsTransitive B).mem_trans hZF (h.subset _ hF)
  obtain ⟨W, hWY, hw⟩ := h.bounded_witness boundedFamilyContainmentFormula_bounded
    ![F, a] (by simp [hF, ha]) ⟨Z, hZB, by simpa [boundedFamilyContainmentFormula] using And.intro hZF haZ⟩
  have hw' : W ∈ F ∧ a ⊆ W := by simpa [boundedFamilyContainmentFormula] using hw
  exact ⟨W, mem_inter_iff.mpr ⟨hw'.1, hWY⟩, hw'.2⟩

include h in
theorem inter_directed_family (hF : F ∈ Y)
    (hdir : ∀ A ∈ F, ∀ C ∈ F, ∃ Z ∈ F, A ⊆ Z ∧ C ⊆ Z) :
    ∀ A ∈ F ∩ Y, ∀ C ∈ F ∩ Y, ∃ Z ∈ F ∩ Y, A ⊆ Z ∧ C ⊆ Z := by
  intro A hA C hC
  obtain ⟨hAF, hAY⟩ := mem_inter_iff.mp hA
  obtain ⟨hCF, hCY⟩ := mem_inter_iff.mp hC
  obtain ⟨Z, hZF, hAZ, hCZ⟩ := hdir A hAF C hCF
  have hZB := (inferInstance : IsTransitive B).mem_trans hZF (h.subset _ hF)
  obtain ⟨W, hWY, hw⟩ := h.bounded_witness boundedFamilyUpperBoundFormula_bounded
    ![F, A, C] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hF, hAY, hCY])
    ⟨Z, hZB, by simpa [boundedFamilyUpperBoundFormula] using And.intro hZF (And.intro hAZ hCZ)⟩
  have hw' : W ∈ F ∧ A ⊆ W ∧ C ⊆ W := by simpa [boundedFamilyUpperBoundFormula] using hw
  exact ⟨W, mem_inter_iff.mpr ⟨hw'.1, hWY⟩, hw'.2⟩

include h in
theorem family_nonempty_directed_intersection (hF : F ∈ Y) (hne : IsNonempty F)
    (hdir : ∀ A ∈ F, ∀ C ∈ F, ∃ Z ∈ F, A ⊆ Z ∧ C ⊆ Z) :
    IsNonempty (F ∩ Y) ∧
      ∀ A ∈ F ∩ Y, ∀ C ∈ F ∩ Y, ∃ Z ∈ F ∩ Y, A ⊆ Z ∧ C ⊆ Z :=
  ⟨h.nonempty_inter_member hF hne, h.inter_directed_family hF hdir⟩

end IsElementaryInclusion
end ZFVP
