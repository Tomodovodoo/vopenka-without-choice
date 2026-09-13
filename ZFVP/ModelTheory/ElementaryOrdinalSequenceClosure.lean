import ZFVP.ModelTheory.ElementaryBoundedWitness
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.FunctionValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSequenceRestrictionFormula : SetTheorySemisentence 4 :=
  “t g η D. !boundedFunctionFormula t η D ∧ !isSubsetOf t g”

theorem boundedSequenceRestrictionFormula_bounded :
    IsBoundedSetFormula boundedSequenceRestrictionFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (isSubsetOf_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsElementaryInclusion.ordinal_sequence_mem {X B η A D t : V}
    (hX : IsElementaryInclusion X B) [IsTransitive B] [IsOrdinal η]
    (h0X : (∅ : V) ∈ X) (hηX : η ∈ X) (hDX : D ∈ X)
    (hclosure : (X ∩ A) ^ (hierarchy η) ⊆ X) (hDA : D ⊆ A)
    (ht : t ∈ (X ∩ D) ^ η) (htB : t ∈ B) : t ∈ X := by
  classical
  by_cases hη : η = ∅
  · have ht0 : t = ∅ := by
      apply SetTheory.subset_antisymm
      · simpa [hη] using subset_prod_of_mem_function ht
      · exact empty_subset _
    exact ht0.symm ▸ h0X
  obtain ⟨i, hi⟩ := (ne_empty_iff_isNonempty.mp hη).nonempty
  let F := fun z ↦ if z ∈ η then t ‘ z else t ‘ i
  have hF : ℒₛₑₜ-function₁ F := by
    have hp : ℒₛₑₜ-relation (fun y z : V ↦
        (z ∈ η ∧ y = t ‘ z) ∨ (z ∉ η ∧ y = t ‘ i)) := by definability
    apply Language.Definable.of_iff hp
    intro v
    change v 0 = F (v 1) ↔ _
    by_cases hv : v 1 ∈ η <;> simp [F, hv]
  let g := definableGraph (hierarchy η) F hF
  have hg : g ∈ (X ∩ D) ^ (hierarchy η) := by
    apply definableGraph_mem_function_of_mapsTo
    intro z _
    dsimp only [F]
    split_ifs with hz
    · exact ZFVP.function_value_mem ht hz
    · exact ZFVP.function_value_mem ht hi
  have hgX : g ∈ X := hclosure g (mem_function_of_mem_function_of_subset hg (by
    intro z hz
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz).1, hDA z (mem_inter_iff.mp hz).2⟩))
  have htD : t ∈ D ^ η := mem_function_of_mem_function_of_subset ht
    (fun z hz ↦ (mem_inter_iff.mp hz).2)
  let := IsFunction.of_mem ht
  have htg : t ⊆ g := by
    intro p hp
    obtain ⟨z, a, rfl⟩ := IsFunction.mem_eq_kpair hp
    apply (pair_mem_definableGraph_iff (hierarchy η) F hF z a).mpr
    have hz := (mem_of_mem_functions ht hp).1
    exact ⟨ordinal_subset_hierarchy η z hz, by simp [F, hz, value_eq_of_kpair_mem hp]⟩
  obtain ⟨s, hsX, hs⟩ := hX.bounded_witness boundedSequenceRestrictionFormula_bounded
    ![g, η, D] (Fin.cases hgX (Fin.cases hηX (Fin.cases hDX (fun i ↦ Fin.elim0 i))))
    ⟨t, htB, by simpa [boundedSequenceRestrictionFormula] using And.intro htD htg⟩
  have hs' : s ∈ D ^ η ∧ s ⊆ g := by
    simpa [boundedSequenceRestrictionFormula] using hs
  let := IsFunction.of_mem hs'.1
  let := IsFunction.of_mem hg
  have heq : s = t := by
    apply function_ext hs'.1 htD
    intro z hz a _ hza
    have hzt : ⟨z, t ‘ z⟩ₖ ∈ t := kpair_value_mem ((domain_eq_of_mem_function ht).symm ▸ hz)
    have hea : a = t ‘ z := IsFunction.unique (hs'.2 _ hza) (htg _ hzt)
    exact hea.symm ▸ hzt
  exact heq ▸ hsX

end ZFVP
