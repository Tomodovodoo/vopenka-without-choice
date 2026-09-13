import ZFVP.ModelTheory.InternalBinaryQuotientAtoms
import ZFVP.SetTheory.InternalChoice

/-! Representative assignments for actual internal quotients. Internal choice
handles arbitrary index sets, including nonstandard finite variable contexts. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_quotientAssignment_of_internalChoice (hAC : InternalChoice V)
    {D E I b : V} (hb : b ∈ internalQuotientCarrier D E ^ I) :
    ∃ a ∈ D ^ I, compose a (internalQuotientProjection D E) = b := by
  let S : V → V := fun i ↦ {x ∈ D ; internalEquivalenceClass D E x = b ‘ i}
  have hS : ℒₛₑₜ-function₁ S := by
    have hr : ℒₛₑₜ-relation (fun X i : V ↦ ∀ x, x ∈ X ↔ x ∈ D ∧ internalEquivalenceClass D E x = b ‘ i) := by definability
    apply Language.Definable.of_iff hr
    intro v
    change v 0 = S (v 1) ↔ _
    rw [mem_ext_iff]
    simp only [S, mem_sep_iff]
  have hn (i : V) (hi : i ∈ I) : IsNonempty (S i) := by
    obtain ⟨x, hx, he⟩ := (mem_internalQuotientCarrier _ _ _).mp (function_value_mem hb hi)
    exact ⟨x, mem_sep_iff.mpr ⟨hx, he.symm⟩⟩
  obtain ⟨a, ha, had, hav⟩ := choice_for_definable_family hAC I S hS hn
  let := ha
  have haD : a ∈ D ^ I := by
    apply mem_function_of_mem_function_of_subset (had ▸ IsFunction.mem_function a)
    intro x hx
    obtain ⟨i, hi⟩ := mem_range_iff.mp hx
    have hiI : i ∈ I := had ▸ mem_domain_of_kpair_mem hi
    have hxD := (mem_sep_iff.mp (hav i hiI)).1
    rwa [value_eq_of_kpair_mem hi] at hxD
  refine ⟨a, haD, ?_⟩
  apply function_eq_of_values (compose_function haD (internalQuotientProjection_mem D E)) hb
  intro i hi
  rw [quotientAssignment_value haD hi]
  exact (mem_sep_iff.mp (hav i hi)).2

end ZFVP
