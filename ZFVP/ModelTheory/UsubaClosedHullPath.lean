import ZFVP.ModelTheory.ElementaryBoundedWitness
import ZFVP.ModelTheory.UsubaCollapseModel
import ZFVP.SetTheory.WellOrderedDependentChoice

/-! The final path construction in Usuba Proposition 4.7. Elementarity
and closure under short sequences make the relation serial on the hull.
The collapse makes that hull well-orderable via its explicit surjection. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def usubaHullSuccessorFormula : SetTheorySemisentence 4 :=
  “x A R s. x ∈ A ∧ !boundedPairMemberFormula R s x”

theorem usubaHullSuccessorFormula_bounded : IsBoundedSetFormula usubaHullSuccessorFormula :=
  .and (.rel _ _) (boundedPairMemberFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_usubaHullSuccessorFormula (v : Fin 4 → V) :
    usubaHullSuccessorFormula.Evalb v ↔ v 0 ∈ v 1 ∧ ⟨v 3, v 0⟩ₖ ∈ v 2 := by
  simp [usubaHullSuccessorFormula]

theorem dependentChoicePath_of_closed_elementary_hull
    {γ A R X B : V} [IsOrdinal γ] [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hAX : A ∈ X) (hRX : R ∈ X)
    (hw : IsWellOrderable X)
    (hclosed : shorterSequences γ (A ∩ X) ⊆ X)
    (hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) :
    ∃ f, IsDependentChoicePath A R γ f ∧ range f ⊆ X := by
  have hsub : A ∩ X ⊆ A := fun x hx ↦ (mem_inter_iff.mp hx).1
  have hsubX : A ∩ X ⊆ X := fun x hx ↦ (mem_inter_iff.mp hx).2
  have hwo : IsWellOrderable (A ∩ X) := by
    obtain ⟨β, hβ, hinj⟩ := (wellOrderable_iff_cardLE_ordinal X).mp hw
    exact (wellOrderable_iff_cardLE_ordinal (A ∩ X)).mpr
      ⟨β, hβ, (cardLE_of_subset hsubX).trans hinj⟩
  have hs : ∀ s ∈ shorterSequences γ (A ∩ X), ∃ x ∈ A ∩ X, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    have hsX := hclosed s hs
    obtain ⟨β, hβ, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    have hsA := (mem_shorterSequences _ _ _).mpr
      ⟨β, hβ, mem_function_of_mem_function_of_subset hsf hsub⟩
    obtain ⟨x, hx, hsx⟩ := hserial s hsA
    have hxB := (inferInstance : IsTransitive B).mem_trans hx (hX.subset _ hAX)
    obtain ⟨y, hyX, hy⟩ := hX.bounded_witness usubaHullSuccessorFormula_bounded
      ![A, R, s] (by
        intro i
        exact Fin.cases hAX (Fin.cases hRX (Fin.cases hsX (fun j ↦ Fin.elim0 j))) i)
      ⟨x, hxB, (eval_usubaHullSuccessorFormula _).mpr ⟨hx, hsx⟩⟩
    have hy' := (eval_usubaHullSuccessorFormula _).mp hy
    exact ⟨y, mem_inter_iff.mpr ⟨hy'.1, hyX⟩, hy'.2⟩
  obtain ⟨f, hf⟩ := dependentChoicePath_of_wellOrderable hwo hs
  exact ⟨f, ⟨mem_function_of_mem_function_of_subset hf.1 hsub, hf.2⟩,
    subset_trans (range_subset_of_mem_function hf.1) hsubX⟩

namespace UsubaCollapseModel

variable {κ S : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (usubaCollapse κ S) (usubaCollapseOrder κ S) G)

theorem dependentChoicePath_of_hull_surjection (hS : IsNonempty S)
    {γ A R X B e : (usubaCollapseContext hκ S G hG).Model}
    [IsOrdinal γ] [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hAX : A ∈ X) (hRX : R ∈ X)
    (he : e ∈ X ^ (usubaCollapseContext hκ S G hG).check S) (hr : range e = X)
    (hclosed : shorterSequences γ (A ∩ X) ⊆ X)
    (hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) :
    ∃ f, IsDependentChoicePath A R γ f ∧ range f ⊆ X :=
  dependentChoicePath_of_closed_elementary_hull hX hAX hRX
    (wellOrderable_of_surjective_function (check_wellOrderable hκ hG hS) he hr)
    hclosed hserial

end UsubaCollapseModel
end ZFVP
