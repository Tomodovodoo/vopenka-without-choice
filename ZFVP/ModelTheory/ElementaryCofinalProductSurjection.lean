import ZFVP.ModelTheory.CollapsedElementarySubmodel
import ZFVP.ModelTheory.ElementaryBoundedWitness

/-! The product-surjection step of Usuba's weak-LS cofinality argument.
The inverse collapse indexes the surjections present in an elementary hull.
An ambient set of functions supplies witnesses for bounded reflection. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSurjectionWitnessFormula : SetTheorySemisentence 3 :=
  “f μ η. !boundedFunctionFormula f μ η ∧ !boundedRangeFormula η f”

theorem boundedSurjectionWitnessFormula_bounded : IsBoundedSetFormula boundedSurjectionWitnessFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (boundedRangeFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSurjectionWitnessFormula (v : Fin 3 → V) :
    boundedSurjectionWitnessFormula.Evalb v ↔ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2 := by
  simp [boundedSurjectionWitnessFormula, eq_comm]

theorem elementaryCofinal_product_surjection {X B C e μ θ : V}
    [IsTransitive B] [IsOrdinal θ]
    (hX : IsElementaryInclusion X B)
    (he : IsTransitiveCollapse (membershipRelation X) X C e)
    (hμ : μ ∈ X) (hpow : θ ^ μ ∈ B) (hzero : (0 : V) ∈ θ)
    (hsurj : ∀ η ∈ θ, IsNonempty η → ∃ f ∈ η ^ μ, range f = η)
    (hcof : ∀ z ∈ θ, ∃ η ∈ X, η ∈ θ ∧ z ∈ η) :
    ∃ g ∈ θ ^ (C ×ˢ μ), range g = θ := by
  classical
  have hfunctions : ∀ η ∈ X, η ∈ θ → IsNonempty η →
      ∃ f ∈ X, f ∈ η ^ μ ∧ range f = η := by
    intro η hηX hηθ hηne
    obtain ⟨f, hf, hfr⟩ := hsurj η hηθ hηne
    have hfθ : f ∈ θ ^ μ := mem_function_of_mem_function_of_subset hf
      (IsOrdinal.toIsTransitive.transitive _ hηθ)
    have hfB := (inferInstance : IsTransitive B).mem_trans hfθ hpow
    obtain ⟨f', hf'X, hf'⟩ := hX.bounded_witness boundedSurjectionWitnessFormula_bounded
      ![μ, η] (by simp [hμ, hηX])
      ⟨f, hfB, (eval_boundedSurjectionWitnessFormula ![f, μ, η]).mpr ⟨hf, hfr⟩⟩
    exact ⟨f', hf'X, (eval_boundedSurjectionWitnessFormula ![f', μ, η]).mp hf'⟩
  let v : V → V := fun p ↦ ((converseGraph e) ‘ (kpair.π₁ p)) ‘ (kpair.π₂ p)
  have hv : ℒₛₑₜ-function₁ v := by unfold v; definability
  let F : V → V := fun p ↦ if v p ∈ θ then v p else 0
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y p : V ↦
        (v p ∈ θ ∧ y = v p) ∨ (v p ∉ θ ∧ y = 0)) := by definability
    apply Language.Definable.of_iff h
    intro w
    change w 0 = F (w 1) ↔ _
    unfold F
    split <;> simp_all
  have hmaps : ∀ p ∈ C ×ˢ μ, F p ∈ θ := by
    intro p _
    dsimp only [F]
    split_ifs with hp
    · exact hp
    · exact hzero
  let g := definableGraph (C ×ˢ μ) F hF
  have hg : g ∈ θ ^ (C ×ˢ μ) := definableGraph_mem_function_of_mapsTo _ _ _ _ hmaps
  refine ⟨g, hg, SetTheory.subset_antisymm (range_subset_of_mem_function hg) ?_⟩
  intro z hz
  obtain ⟨η, hηX, hηθ, hzη⟩ := hcof z hz
  obtain ⟨f, hfX, hf, hfr⟩ := hfunctions η hηX hηθ ⟨z, hzη⟩
  let := IsFunction.of_mem hf
  obtain ⟨i, hiz⟩ := mem_range_iff.mp (hfr.symm ▸ hzη)
  have hiμ : i ∈ μ := (mem_of_mem_functions hf hiz).1
  have hvz : v ⟨e ‘ f, i⟩ₖ = z := by
    simp only [v, kpair.π₁_kpair, kpair.π₂_kpair, transitiveCollapse_inverse_value he hfX]
    exact value_eq_of_kpair_mem hiz
  have hp : ⟨e ‘ f, i⟩ₖ ∈ C ×ˢ μ :=
    kpair_mem_iff.mpr ⟨function_value_mem he.2.1 hfX, hiμ⟩
  apply mem_range_of_kpair_mem (x := ⟨e ‘ f, i⟩ₖ)
  exact (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hp, by simp [F, hvz, hz]⟩

end ZFVP
