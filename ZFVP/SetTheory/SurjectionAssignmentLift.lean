import ZFVP.SetTheory.ChoiceDictionary
import ZFVP.SetTheory.FunctionUnion

/-! Internal choice lifts actual assignments through an actual surjection.
The index set is arbitrary, including nonstandard internally finite sets. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_assignment_lift_of_surjection (hAC : InternalChoice V) {A B I q b : V}
    (hq : q ∈ B ^ A) (hqr : range q = B) (hb : b ∈ B ^ I) :
    ∃ c ∈ A ^ I, compose c q = b := by
  let F : V → V := fun i ↦ {x ∈ A ; q ‘ x = b ‘ i}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ x, x ∈ S ↔ x ∈ A ∧ q ‘ x = b ‘ i) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hne : ∀ i ∈ I, IsNonempty (F i) := by
    intro i hi
    have hir : b ‘ i ∈ range q := hqr ▸ function_value_mem hb hi
    obtain ⟨x, hx⟩ := mem_range_iff.mp hir
    let : IsFunction q := IsFunction.of_mem hq
    exact ⟨x, mem_sep_iff.mpr ⟨(mem_of_mem_functions hq hx).1, value_eq_of_kpair_mem hx⟩⟩
  obtain ⟨c, hc, hdom, hchoice⟩ := choice_for_definable_family hAC I F hF hne
  let : IsFunction c := hc
  have hv : ∀ i ∈ I, c ‘ i ∈ A ∧ q ‘ (c ‘ i) = b ‘ i := fun i hi ↦ mem_sep_iff.mp (hchoice i hi)
  have hrange : range c ⊆ A := by
    intro x hx
    obtain ⟨i, hix⟩ := mem_range_iff.mp hx
    have hi : i ∈ I := hdom ▸ mem_domain_of_kpair_mem hix
    simpa only [value_eq_of_kpair_mem hix] using (hv i hi).1
  have hcA : c ∈ A ^ I := by
    simpa only [hdom] using mem_function_of_mem_function_of_subset (IsFunction.mem_function c) hrange
  have hcq := compose_function hcA hq
  let : IsFunction (compose c q) := IsFunction.of_mem hcq
  let : IsFunction b := IsFunction.of_mem hb
  refine ⟨c, hcA, functions_eq_of_domain_values (by rw [domain_eq_of_mem_function hcq, domain_eq_of_mem_function hb]) ?_⟩
  intro i hi
  have hiI : i ∈ I := by simpa only [domain_eq_of_mem_function hcq] using hi
  rw [value_compose_of_mem_function hcA hq hiI]
  exact (hv i hiI).2

end ZFVP
