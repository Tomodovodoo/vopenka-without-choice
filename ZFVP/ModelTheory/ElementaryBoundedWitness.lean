import ZFVP.ModelTheory.ElementaryInclusionLaws
import ZFVP.ModelTheory.EmbeddingBoundedOperations
import ZFVP.SetTheory.BoundedRelationRange

/-! Elementary submodels of a transitive set contain witnesses to bounded
relations with their parameters, whenever a witness exists in the ambient set. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {X B : V} (h : IsElementaryInclusion X B)

theorem eval_semisentence_inclusion {n : ℕ} (φ : SetTheorySemisentence n)
    (b : Fin n → SetDomain X) :
    φ.Evalb b ↔ φ.Evalb (M := SetDomain B) (fun i ↦ (⟨(b i).val, h.subset _ (b i).property⟩ : SetDomain B)) := by
  have hv : h.toFunction ∘ b =
      (fun i ↦ (⟨(b i).val, h.subset _ (b i).property⟩ : SetDomain B)) := by
    funext i
    apply Subtype.ext
    exact identity_value (b i).property
  rw [← hv]
  exact h.eval_semisentence φ b

include h in
theorem bounded_witness [IsTransitive B] {n : ℕ} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → V) (hv : ∀ i, v i ∈ X)
    (hex : ∃ y ∈ B, φ.Evalb (Matrix.vecCons y v)) :
    ∃ y ∈ X, φ.Evalb (Matrix.vecCons y v) := by
  let b : Fin n → SetDomain X := fun i ↦ ⟨v i, hv i⟩
  have hs : (φ.exs).Evalb (M := SetDomain B) (fun i ↦ (⟨v i, h.subset _ (hv i)⟩ : SetDomain B)) := by
    obtain ⟨y, hy, hpy⟩ := hex
    change ∃ y : SetDomain B, φ.Evalb (Matrix.vecCons y _) 
    refine ⟨⟨y, hy⟩, ?_⟩
    apply (bounded_formula_absolute B hφ _).mpr
    convert hpy using 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  have hsX := (h.eval_semisentence_inclusion φ.exs b).mpr hs
  change ∃ y : SetDomain X, φ.Evalb (Matrix.vecCons y b) at hsX
  obtain ⟨y, hy⟩ := hsX
  refine ⟨y.val, y.property, ?_⟩
  have ht := (h.eval_semisentence_inclusion φ (Matrix.vecCons y b)).mp hy
  have htV := (bounded_formula_absolute B hφ _).mp ht
  convert htV using 1
  congr 1
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

include h in
theorem function_value_mem [IsTransitive B] {f x : V}
    (hfX : f ∈ X) (hxX : x ∈ X) [IsFunction f] (hx : x ∈ domain f) : f ‘ x ∈ X := by
  have hpair : ⟨x, f ‘ x⟩ₖ ∈ f := kpair_value_mem hx
  have hyB : f ‘ x ∈ B := (kpair_components_mem_transitive
    ((inferInstance : IsTransitive B).mem_trans hpair (h.subset _ hfX))).2
  obtain ⟨y, hyX, hpy⟩ := h.bounded_witness
    (boundedPairMemberFormula_bounded.subst ![.bvar 1, .bvar 2, .bvar 0])
    ![f, x] (by simp [hfX, hxX]) ⟨f ‘ x, hyB, by simpa using hpair⟩
  have hxy : ⟨x, y⟩ₖ ∈ f := by simpa using hpy
  exact (value_eq_of_kpair_mem hxy).symm ▸ hyX

include h in
theorem range_mem [IsTransitive B] {f : V}
    (hf : f ∈ X) (hr : range f ∈ B) : range f ∈ X := by
  obtain ⟨y, hy, he⟩ := h.bounded_witness boundedRangeFormula_bounded
    ![f] (by simpa using hf) ⟨range f, hr, (Defined.eval_iff (R := fun v : Fin 2 → V ↦ v 0 = range (v 1)) _).mpr rfl⟩
  have heq : y = range f := (Defined.eval_iff _).mp he
  exact heq ▸ hy
end IsElementaryInclusion
end ZFVP






