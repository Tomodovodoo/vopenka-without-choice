import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.SetTheory.FiniteSets

/-! Internal finite demands have strict upper bounds in the directed posets
used in the Rubin background, and internal choice selects all bounds at once. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalDirectedNoMax.finite_upper_bound {P R S : V}
    (h : IsInternalDirectedNoMax P R) (hR : IsForcingPreorder P R)
    (hS : IsInternallyFinite S) (hSP : S ⊆ P) : ∃ z ∈ P, ∀ x ∈ S, ⟨x, z⟩ₖ ∈ R := by
  have hall : ∀ S, IsInternallyFinite S → S ⊆ P → ∃ z ∈ P, ∀ x ∈ S, ⟨x, z⟩ₖ ∈ R := by
    apply internallyFinite_induction (fun S ↦ S ⊆ P → ∃ z ∈ P, ∀ x ∈ S, ⟨x, z⟩ₖ ∈ R) (by definability)
    · intro _
      obtain ⟨z, hz⟩ := h.1
      exact ⟨z, hz, fun _ hx ↦ False.elim (not_mem_empty hx)⟩
    · intro S a ih hsub
      obtain ⟨z, hz, hSz⟩ := ih (fun x hx ↦ hsub x (mem_insert.mpr (Or.inr hx)))
      obtain ⟨w, hw, hzw, haw⟩ := h.2.1 z hz a (hsub a (by simp))
      refine ⟨w, hw, ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact haw
      · exact hR.2.2 x (hsub x (mem_insert.mpr (Or.inr hx))) z hz w hw (hSz x hx) hzw
  exact hall S hS hSP

theorem IsInternalDirectedNoMax.strict_upper {P R x : V}
    (h : IsInternalDirectedNoMax P R) (hx : x ∈ P) : ∃ z ∈ P, ⟨x, z⟩ₖ ∈ R ∧ x ≠ z := by
  classical
  have he : ∃ y ∈ P, ⟨y, x⟩ₖ ∉ R := by
    by_contra hn
    apply h.2.2
    exact ⟨x, hx, fun y hy ↦ by by_contra hh; exact hn ⟨y, hy, hh⟩⟩
  obtain ⟨y, hy, hyx⟩ := he
  obtain ⟨z, hz, hxz, hyz⟩ := h.2.1 x hx y hy
  exact ⟨z, hz, hxz, fun hh ↦ hyx (hh.symm ▸ hyz)⟩

theorem IsInternalDirectedNoMax.finite_strict_upper_bound {P R S : V}
    (h : IsInternalDirectedNoMax P R) (hR : IsForcingPoset P R)
    (hS : IsInternallyFinite S) (hSP : S ⊆ P) :
    ∃ z ∈ P, ∀ x ∈ S, ⟨x, z⟩ₖ ∈ R ∧ x ≠ z := by
  obtain ⟨y, hy, hSy⟩ := h.finite_upper_bound hR.1 hS hSP
  obtain ⟨z, hz, hyz, hyne⟩ := h.strict_upper hy
  refine ⟨z, hz, fun x hx ↦ ⟨hR.1.2.2 x (hSP x hx) y hy z hz (hSy x hx) hyz, ?_⟩⟩
  intro hxz
  exact hyne (hR.2 y hy z hz hyz (hxz ▸ hSy x hx))

theorem exists_finite_strict_upper_choice (hAC : InternalChoice V) {I D P R A : V}
    (hP : P ∈ power D ^ I)
    (hpos : ∀ i ∈ I, IsForcingPoset (P ‘ i) (R ‘ i))
    (hdir : ∀ i ∈ I, IsInternalDirectedNoMax (P ‘ i) (R ‘ i))
    (hA : IsInternallyFinite A) (hAI : A ⊆ I ×ˢ D)
    (hvalid : ∀ i x, ⟨i, x⟩ₖ ∈ A → x ∈ P ‘ i) :
    ∃ c ∈ D ^ I, (∀ i ∈ I, c ‘ i ∈ P ‘ i) ∧
      ∀ i x, ⟨i, x⟩ₖ ∈ A → ⟨x, c ‘ i⟩ₖ ∈ R ‘ i ∧ x ≠ c ‘ i := by
  let F : V → V := fun i ↦ {z ∈ P ‘ i ; ∀ x, ⟨i, x⟩ₖ ∈ A → ⟨x, z⟩ₖ ∈ R ‘ i ∧ x ≠ z}
  have hF : ℒₛₑₜ-function₁ F := by
    have hh : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ z, z ∈ S ↔ z ∈ P ‘ i ∧
      ∀ x, ⟨i, x⟩ₖ ∈ A → ⟨x, z⟩ₖ ∈ R ‘ i ∧ x ≠ z) := by definability
    apply Language.Definable.of_iff hh
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hne : ∀ i ∈ I, IsNonempty (F i) := by
    intro i hi
    let S := {x ∈ P ‘ i ; ⟨i, x⟩ₖ ∈ A}
    have hS : IsInternallyFinite S := internallyFinite_subset (internallyFinite_range hA)
      (fun x hx ↦ mem_range_of_kpair_mem (mem_sep_iff.mp hx).2)
    obtain ⟨z, hz, hbound⟩ := (hdir i hi).finite_strict_upper_bound (hpos i hi) hS
      (fun _ hx ↦ (mem_sep_iff.mp hx).1)
    exact ⟨z, mem_sep_iff.mpr ⟨hz, fun x hx ↦ hbound x (mem_sep_iff.mpr ⟨hvalid i x hx, hx⟩)⟩⟩
  obtain ⟨c, hc, hdom, hchoice⟩ := choice_for_definable_family hAC I F hF hne
  let : IsFunction c := hc
  have hvalues : ∀ i ∈ I, c ‘ i ∈ P ‘ i ∧
      ∀ x, ⟨i, x⟩ₖ ∈ A → ⟨x, c ‘ i⟩ₖ ∈ R ‘ i ∧ x ≠ c ‘ i :=
    fun i hi ↦ mem_sep_iff.mp (hchoice i hi)
  have hrange : range c ⊆ D := by
    intro x hx
    obtain ⟨i, hix⟩ := mem_range_iff.mp hx
    have hi : i ∈ I := hdom ▸ mem_domain_of_kpair_mem hix
    have hxP := (hvalues i hi).1
    rw [value_eq_of_kpair_mem hix] at hxP
    exact mem_power_iff.mp (function_value_mem hP hi) x hxP
  refine ⟨c, ?_, fun i hi ↦ (hvalues i hi).1, fun i x hx ↦ ?_⟩
  · simpa only [hdom] using mem_function_of_mem_function_of_subset (IsFunction.mem_function c) hrange
  · exact (hvalues i (kpair_mem_iff.mp (hAI _ hx)).1).2 x hx

end ZFVP.Schmerl
