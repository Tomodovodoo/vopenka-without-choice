import ZFVP.ModelTheory.ReflectedPairWitnessTable
import ZFVP.SetTheory.BoundedSequenceSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {X B : V} (h : IsElementaryInclusion X B) [IsSequenceSupport B]
include h

theorem singleton_mem_of_sequenceSupport {x : V} (hx : x ∈ X) : ({x} : V) ∈ X := by
  obtain ⟨y, hy, he⟩ := h.bounded_witness boundedDoubletonFormula_bounded
    ![x, x] (by simpa using hx)
    ⟨({x} : V), IsCodingSupport.singleton_mem (h.subset x hx), by simp [singleton_def]⟩
  have heq : y = ({x} : V) := by simpa [singleton_def] using he
  exact heq ▸ hy

theorem union_mem_of_sequenceSupport {x y : V} (hx : x ∈ X) (hy : y ∈ X) : x ∪ y ∈ X := by
  obtain ⟨z, hz, he⟩ := h.bounded_witness boundedUnionFormula_bounded
    ![x, y] (by simp [hx, hy])
    ⟨x ∪ y, IsSequenceSupport.union_closed x (h.subset x hx) y (h.subset y hy),
      (Defined.eval_iff (R := fun v : Fin 3 → V ↦ v 0 = v 1 ∪ v 2) _).mpr rfl⟩
  have heq : z = x ∪ y := (Defined.eval_iff _).mp he
  exact heq ▸ hz

theorem finiteSequences_subset (hω : (ω : V) ⊆ X) : finiteSequences X ⊆ X := by
  apply finiteSequence_induction X (fun s : V ↦ s ∈ X) (by definability) (hω _ empty_mem_ω)
  intro n hn s _ x hx hs
  have hp := h.kpair_mem (hω n hn) hx
    (IsCodingSupport.kpair_closed n (IsCodingSupport.natural_mem hn) x (h.subset x hx))
  exact h.union_mem_of_sequenceSupport (h.singleton_mem_of_sequenceSupport hp) hs

theorem finite_function_mem (hω : (ω : V) ⊆ X) {n s : V}
    (hn : n ∈ (ω : V)) (hs : s ∈ X ^ n) : s ∈ X :=
  h.finiteSequences_subset hω s ((mem_finiteSequences_iff X s).mpr ⟨n, hn, hs⟩)

end IsElementaryInclusion

theorem IsElementaryInclusion.finite_function_mem_of_support {X B U n s : V}
    [IsTransitive B] [IsSequenceSupport U] (h : IsElementaryInclusion X B)
    (hUX : U ∈ X) (hω : (ω : V) ⊆ X)
    (hn : n ∈ (ω : V)) (hs : s ∈ (X ∩ U) ^ n) : s ∈ X := by
  have hUB : U ⊆ B := (inferInstance : IsTransitive B).transitive U (h.subset U hUX)
  have hall : ∀ t ∈ finiteSequences (X ∩ U), t ∈ X ∧ t ∈ U := by
    apply finiteSequence_induction (X ∩ U) (fun t : V ↦ t ∈ X ∧ t ∈ U) (by definability)
      ⟨hω _ empty_mem_ω, IsCodingSupport.empty_mem⟩
    intro m hm t _ x hx ht
    obtain ⟨hxX, hxU⟩ := mem_inter_iff.mp hx
    have hpU := IsCodingSupport.kpair_closed m (IsCodingSupport.natural_mem hm) x hxU
    have hpX := h.kpair_mem (hω m hm) hxX (hUB _ hpU)
    have hzU := IsCodingSupport.singleton_mem hpU
    obtain ⟨z, hz, he⟩ := h.bounded_witness boundedDoubletonFormula_bounded
      ![⟨m, x⟩ₖ, ⟨m, x⟩ₖ] (by simpa using hpX)
      ⟨({⟨m, x⟩ₖ} : V), hUB _ hzU, by simp [singleton_def]⟩
    have hez : z = ({⟨m, x⟩ₖ} : V) := by simpa [singleton_def] using he
    subst z
    have hvU := IsSequenceSupport.union_closed _ hzU t ht.2
    obtain ⟨v, hv, he⟩ := h.bounded_witness boundedUnionFormula_bounded
      ![({⟨m, x⟩ₖ} : V), t] (by simp [hz, ht.1])
      ⟨insert ⟨m, x⟩ₖ t, hUB _ hvU,
        (Defined.eval_iff (R := fun v : Fin 3 → V ↦ v 0 = v 1 ∪ v 2) _).mpr rfl⟩
    have hev : v = insert ⟨m, x⟩ₖ t := (Defined.eval_iff _).mp he
    exact ⟨hev ▸ hv, hvU⟩
  exact (hall s ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, hs⟩)).1
end ZFVP
