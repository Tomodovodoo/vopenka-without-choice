import ZFVP.ModelTheory.TransitiveZFForcingOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingClassUnion_names_val (P : SetDomain U)
    (f : SetDomain U → SetDomain U) (hf : ℒₛₑₜ-function₁ f)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (he : ∀ x, (f x).val = F x.val) :
    (forcingClassUnion P (IsForcingName P) (by definability) f hf).val =
      forcingClassUnion P.val (fun x ↦ x ∈ U ∧ IsForcingName P.val x) (by definability) F hF := by
  unfold forcingClassUnion
  apply sep_val U
  intro p _
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x.val, ⟨x.property, (forcingName_iff U P x).mp hx⟩, he x ▸ hp⟩
  · rintro ⟨x, ⟨hxU, hx⟩, hp⟩
    let x' : SetDomain U := ⟨x, hxU⟩
    refine ⟨x', (forcingName_iff U P x').mpr hx, ?_⟩
    change p.val ∈ (f x').val
    rwa [he x']

theorem forcingClassIntersection_names_val (P : SetDomain U)
    (f : SetDomain U → SetDomain U) (hf : ℒₛₑₜ-function₁ f)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (he : ∀ x, (f x).val = F x.val) :
    (forcingClassIntersection P (IsForcingName P) (by definability) f hf).val =
      forcingClassIntersection P.val (fun x ↦ x ∈ U ∧ IsForcingName P.val x) (by definability) F hF := by
  unfold forcingClassIntersection
  apply sep_val U
  intro p _
  constructor
  · intro h x hx
    let x' : SetDomain U := ⟨x, hx.1⟩
    have hp := h x' ((forcingName_iff U P x').mpr hx.2)
    change p.val ∈ (f x').val at hp
    rwa [he x'] at hp
  · intro h x hx
    change p.val ∈ (f x).val
    rw [he x]
    exact h x.val ⟨x.property, (forcingName_iff U P x).mp hx⟩

theorem forcingFormula_standardTuple_val (P R : SetDomain U)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → SetDomain U) :
    (forcingFormula P R φ (standardTuple v)).val =
      classForcingFormula P.val R.val (fun x ↦ x ∈ U ∧ IsForcingName P.val x)
        (by definability) φ (standardTuple (fun i ↦ (v i).val)) := by
  induction φ with
  | verum => rfl
  | falsum => exact empty_val U
  | rel r ts =>
    simp only [forcingFormula_rel, classForcingFormula_rel, forcingAtomic_val U, standardTuple_val U]
  | nrel r ts =>
    simp only [forcingFormula_nrel, classForcingFormula_nrel, forcingNegation_val U,
      forcingAtomic_val U, standardTuple_val U]
  | and φ ψ ihφ ihψ =>
    simp only [forcingFormula_and, classForcingFormula_and, inter_val U, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    simp only [forcingFormula_or, classForcingFormula_or, forcingClosure_val U, union_val U, ihφ, ihψ]
  | @all n φ ih =>
    rw [forcingFormula_all, classForcingFormula_all]
    apply forcingClassIntersection_names_val U
    intro x
    exact ih (Matrix.vecCons x v)
  | @exs n φ ih =>
    rw [forcingFormula_exs, classForcingFormula_exs]
    unfold forcingExistential
    rw [forcingClosure_val U]
    congr 1
    apply forcingClassUnion_names_val U
    intro x
    exact ih (Matrix.vecCons x v)

end TransitiveZF
end ZFVP
