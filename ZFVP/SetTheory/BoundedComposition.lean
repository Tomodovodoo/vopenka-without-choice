import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.FunctionComposition

/-! A bounded test for composition between typed function graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedComposedAssignmentFormula : SetTheorySemisentence 6 :=
  “n A B b f c. !boundedFunctionFormula c n B ∧
    ∀ i ∈ n, ∀ x ∈ A, ∀ y ∈ B,
      !boundedPairMemberFormula b i x → !boundedPairMemberFormula f x y →
        !boundedPairMemberFormula c i y”

theorem boundedComposedAssignmentFormula_bounded : IsBoundedSetFormula boundedComposedAssignmentFormula :=
  .and (boundedFunctionFormula_bounded.subst _)
    (.all (.bvar 0) (.all (.bvar 2) (.all (.bvar 4)
      (.or (boundedPairMemberFormula_bounded.subst _).neg
        (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedPairMemberFormula_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsComposedAssignment (n A B b f c : V) : Prop :=
  c ∈ B ^ n ∧ ∀ i ∈ n, ∀ x ∈ A, ∀ y ∈ B, ⟨i, x⟩ₖ ∈ b → ⟨x, y⟩ₖ ∈ f → ⟨i, y⟩ₖ ∈ c

instance boundedComposedAssignmentFormula_defined : Defined
    (fun v : Fin 6 → V ↦ IsComposedAssignment (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    boundedComposedAssignmentFormula :=
  ⟨fun v ↦ by simp [boundedComposedAssignmentFormula, IsComposedAssignment]⟩

theorem isComposedAssignment_iff {n A B b f c : V} (hb : b ∈ A ^ n) (hf : f ∈ B ^ A) :
    IsComposedAssignment n A B b f c ↔ c = compose b f := by
  constructor
  · rintro ⟨hc, h⟩
    have hsub : compose b f ⊆ c := by
      intro p hp
      obtain ⟨i, x, y, hib, hxf, rfl⟩ := mem_compose_iff.mp hp
      exact h i (mem_of_mem_functions hb hib).1 x (mem_of_mem_functions hb hib).2
        y (mem_of_mem_functions hf hxf).2 hib hxf
    exact (function_eq_of_subset (compose_function hb hf) hc hsub).symm
  · rintro rfl
    exact ⟨compose_function hb hf, fun i _ x _ y _ hib hxf ↦
      kpair_mem_compose_iff.mpr ⟨x, hib, hxf⟩⟩

end ZFVP
