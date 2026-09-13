import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.CompositionLaws
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingAutomorphism (P R π : V) : Prop :=
  π ∈ P ^ P ∧ Injective π ∧ range π = P ∧
    ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R ↔ ⟨π ‘ p, π ‘ q⟩ₖ ∈ R

instance isForcingAutomorphism_definable : ℒₛₑₜ-relation₃[V] IsForcingAutomorphism := by
  unfold IsForcingAutomorphism
  definability

noncomputable def forcingAutomorphisms (P R : V) : V := {π ∈ P ^ P ; IsForcingAutomorphism P R π}

theorem mem_forcingAutomorphisms_iff (P R π : V) : π ∈ forcingAutomorphisms P R ↔ IsForcingAutomorphism P R π := by
  simp only [forcingAutomorphisms, mem_sep_iff]
  exact ⟨And.right, fun h ↦ ⟨h.1, h⟩⟩

instance forcingAutomorphisms_definable : ℒₛₑₜ-function₂[V] forcingAutomorphisms := by
  have h : ℒₛₑₜ-relation₃ (fun A P R : V ↦ ∀ π, π ∈ A ↔ IsForcingAutomorphism P R π) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingAutomorphisms (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_forcingAutomorphisms_iff]

theorem forcingAutomorphism_identity (P R : V) : IsForcingAutomorphism P R (identity P) := by
  refine ⟨identity_mem_function P, identity_injective P, ?_, ?_⟩
  · apply SetTheory.mem_ext_iff.mpr
    intro p
    simp [mem_range_iff]
  · intro p hp q hq
    rw [identity_value hp, identity_value hq]

theorem forcingAutomorphism_surjective {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    ∀ q ∈ P, ∃ p ∈ P, π ‘ p = q := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  intro q hq
  obtain ⟨p, hp⟩ := mem_range_iff.mp (hπ.2.2.1.symm ▸ hq)
  exact ⟨p, (mem_of_mem_functions hπ.1 hp).1, value_eq_of_kpair_mem hp⟩

theorem forcingAutomorphism_compose {P R π ρ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingAutomorphism P R ρ) : IsForcingAutomorphism P R (compose π ρ) := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  have : IsFunction ρ := IsFunction.of_mem hρ.1
  have hf := compose_function hπ.1 hρ.1
  have : IsFunction (compose π ρ) := IsFunction.of_mem hf
  refine ⟨hf, compose_injective hπ.2.1 hρ.2.1, ?_, ?_⟩
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro r hr
    obtain ⟨q, hq, hqr⟩ := forcingAutomorphism_surjective hρ r hr
    obtain ⟨p, hp, hpq⟩ := forcingAutomorphism_surjective hπ q hq
    have he : (compose π ρ) ‘ p = r := by rw [value_compose_of_mem_function hπ.1 hρ.1 hp, hpq, hqr]
    exact he ▸ value_mem_range hf hp
  · intro p hp q hq
    rw [value_compose_of_mem_function hπ.1 hρ.1 hp, value_compose_of_mem_function hπ.1 hρ.1 hq]
    exact (hπ.2.2.2 p hp q hq).trans
      (hρ.2.2.2 _ (function_value_mem hπ.1 hp) _ (function_value_mem hπ.1 hq))

theorem forcingAutomorphism_inverse {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    IsForcingAutomorphism P R (converseGraph π) := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  have hi : converseGraph π ∈ P ^ P := by
    simpa only [hπ.2.2.1] using converseGraph_mem_function hπ.1 hπ.2.1
  refine ⟨hi, converseGraph_injective π, ?_, ?_⟩
  · rw [range_converseGraph, domain_eq_of_mem_function hπ.1]
  · intro p hp q hq
    have hp' : p ∈ range π := hπ.2.2.1.symm ▸ hp
    have hq' : q ∈ range π := hπ.2.2.1.symm ▸ hq
    simpa only [value_converseGraph_value hπ.1 hπ.2.1 hp', value_converseGraph_value hπ.1 hπ.2.1 hq']
      using (hπ.2.2.2 _ (function_value_mem hi hp) _ (function_value_mem hi hq)).symm

theorem forcingAutomorphism_compose_inverse {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    compose π (converseGraph π) = identity P := by
  have hi := (forcingAutomorphism_inverse hπ).1
  have : IsFunction (compose π (converseGraph π)) := IsFunction.of_mem (compose_function hπ.1 hi)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function hπ.1 hi), domain_eq_of_mem_function (identity_mem_function P)]
  · intro p hp
    have hpP : p ∈ P := domain_eq_of_mem_function (compose_function hπ.1 hi) ▸ hp
    rw [value_compose_of_mem_function hπ.1 hi hpP, converseGraph_value_value hπ.1 hπ.2.1 hpP,
      identity_value hpP]

theorem forcingAutomorphism_inverse_compose {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    compose (converseGraph π) π = identity P := by
  have hi := (forcingAutomorphism_inverse hπ).1
  have : IsFunction (compose (converseGraph π) π) := IsFunction.of_mem (compose_function hi hπ.1)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function hi hπ.1), domain_eq_of_mem_function (identity_mem_function P)]
  · intro p hp
    have hpP : p ∈ P := domain_eq_of_mem_function (compose_function hi hπ.1) ▸ hp
    rw [value_compose_of_mem_function hi hπ.1 hpP, identity_value hpP]
    exact value_converseGraph_value hπ.1 hπ.2.1 (hπ.2.2.1.symm ▸ hpP)

theorem forcingAutomorphism_top {P R one π : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π) : π ‘ one = one := by
  have hπone := function_value_mem hπ.1 hone.1
  apply hR.2 _ hπone one hone.1 (hone.2 _ hπone)
  obtain ⟨p, hp, he⟩ := forcingAutomorphism_surjective hπ one hone.1
  simpa only [he] using (hπ.2.2.2 p hp one hone.1).mp (hone.2 p hp)

end ZFVP
