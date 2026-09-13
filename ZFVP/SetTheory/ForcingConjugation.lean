import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def conjugatePermutation (π ρ : V) : V := compose (compose (converseGraph π) ρ) π

instance conjugatePermutation_definable : ℒₛₑₜ-function₂[V] conjugatePermutation := by
  unfold conjugatePermutation
  definability

theorem conjugatePermutation_automorphism {P R π ρ : V}
    (hπ : IsForcingAutomorphism P R π) (hρ : IsForcingAutomorphism P R ρ) :
    IsForcingAutomorphism P R (conjugatePermutation π ρ) :=
  forcingAutomorphism_compose (forcingAutomorphism_compose (forcingAutomorphism_inverse hπ) hρ) hπ

theorem conjugatePermutation_value {P R π ρ p : V}
    (hπ : IsForcingAutomorphism P R π) (hρ : IsForcingAutomorphism P R ρ) (hp : p ∈ P) :
    (conjugatePermutation π ρ) ‘ p = π ‘ (ρ ‘ ((converseGraph π) ‘ p)) := by
  unfold conjugatePermutation
  rw [value_compose_of_mem_function (compose_function (forcingAutomorphism_inverse hπ).1 hρ.1) hπ.1 hp,
    value_compose_of_mem_function (forcingAutomorphism_inverse hπ).1 hρ.1 hp]

theorem conjugatePermutation_identity {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    conjugatePermutation π (identity P) = identity P := by
  unfold conjugatePermutation
  rw [graph_compose_identity (forcingAutomorphism_inverse hπ).1, forcingAutomorphism_inverse_compose hπ]

theorem conjugatePermutation_compose {P R π ρ σ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingAutomorphism P R ρ) (hσ : IsForcingAutomorphism P R σ) :
    conjugatePermutation π (compose ρ σ) =
      compose (conjugatePermutation π ρ) (conjugatePermutation π σ) := by
  have hi := forcingAutomorphism_inverse hπ
  have hρ' := conjugatePermutation_automorphism hπ hρ
  have hσ' := conjugatePermutation_automorphism hπ hσ
  have hl := conjugatePermutation_automorphism hπ (forcingAutomorphism_compose hρ hσ)
  have hr := forcingAutomorphism_compose hρ' hσ'
  have : IsFunction (conjugatePermutation π (compose ρ σ)) := IsFunction.of_mem hl.1
  have : IsFunction (compose (conjugatePermutation π ρ) (conjugatePermutation π σ)) := IsFunction.of_mem hr.1
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hl.1, domain_eq_of_mem_function hr.1]
  · intro p hp
    have hpP : p ∈ P := domain_eq_of_mem_function hl.1 ▸ hp
    rw [conjugatePermutation_value hπ (forcingAutomorphism_compose hρ hσ) hpP,
      value_compose_of_mem_function hρ.1 hσ.1 (function_value_mem hi.1 hpP),
      value_compose_of_mem_function hρ'.1 hσ'.1 hpP,
      conjugatePermutation_value hπ hσ (function_value_mem hρ'.1 hpP),
      conjugatePermutation_value hπ hρ hpP,
      converseGraph_value_value hπ.1 hπ.2.1 (function_value_mem hρ.1 (function_value_mem hi.1 hpP))]

theorem conjugatePermutation_inverse {P R π ρ : V}
    (hπ : IsForcingAutomorphism P R π) (hρ : IsForcingAutomorphism P R ρ) :
    conjugatePermutation π (converseGraph ρ) = converseGraph (conjugatePermutation π ρ) := by
  have hρ' := conjugatePermutation_automorphism hπ hρ
  have hl := conjugatePermutation_automorphism hπ (forcingAutomorphism_inverse hρ)
  have hr := forcingAutomorphism_inverse hρ'
  have hi := forcingAutomorphism_inverse hπ
  have hρi := forcingAutomorphism_inverse hρ
  have : IsFunction (conjugatePermutation π (converseGraph ρ)) := IsFunction.of_mem hl.1
  have : IsFunction (converseGraph (conjugatePermutation π ρ)) := IsFunction.of_mem hr.1
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hl.1, domain_eq_of_mem_function hr.1]
  · intro p hp
    have hpP : p ∈ P := domain_eq_of_mem_function hl.1 ▸ hp
    apply injective_value_eq hρ'.1 hρ'.2.1 (function_value_mem hl.1 hpP) (function_value_mem hr.1 hpP)
    rw [conjugatePermutation_value hπ hρ (function_value_mem hl.1 hpP),
      conjugatePermutation_value hπ hρi hpP,
      converseGraph_value_value hπ.1 hπ.2.1 (function_value_mem hρi.1 (function_value_mem hi.1 hpP)),
      value_converseGraph_value hρ.1 hρ.2.1 (hρ.2.2.1.symm ▸ function_value_mem hi.1 hpP),
      value_converseGraph_value hπ.1 hπ.2.1 (hπ.2.2.1.symm ▸ hpP),
      value_converseGraph_value hρ'.1 hρ'.2.1 (hρ'.2.2.1.symm ▸ hpP)]

theorem mem_conjugateSubgroup (π H θ : V) :
    θ ∈ conjugateSubgroup π H ↔ ∃ ρ ∈ H, θ = conjugatePermutation π ρ := repl_spec _

theorem converseGraph_involutive (f : V) [IsFunction f] :
    converseGraph (converseGraph f) = f := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    exact (pair_mem_converseGraph f y x).mp ((pair_mem_converseGraph (converseGraph f) x y).mp hz)
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_converseGraph (converseGraph f) x y).mpr ((pair_mem_converseGraph f y x).mpr hz)

theorem conjugatePermutation_cancel_inverse {P R π ρ : V}
    (hπ : IsForcingAutomorphism P R π) (hρ : IsForcingAutomorphism P R ρ) :
    conjugatePermutation π (conjugatePermutation (converseGraph π) ρ) = ρ := by
  have hi := forcingAutomorphism_inverse hπ
  have hc := conjugatePermutation_automorphism hi hρ
  have hl := conjugatePermutation_automorphism hπ hc
  have : IsFunction π := IsFunction.of_mem hπ.1
  have : IsFunction ρ := IsFunction.of_mem hρ.1
  have : IsFunction (conjugatePermutation π (conjugatePermutation (converseGraph π) ρ)) := IsFunction.of_mem hl.1
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hl.1, domain_eq_of_mem_function hρ.1]
  · intro p hp
    have hpP : p ∈ P := domain_eq_of_mem_function hl.1 ▸ hp
    have hcancel : π ‘ ((converseGraph π) ‘ p) = p :=
      value_converseGraph_value hπ.1 hπ.2.1 (hπ.2.2.1.symm ▸ hpP)
    rw [conjugatePermutation_value hπ hc hpP,
      conjugatePermutation_value hi hρ (function_value_mem hi.1 hpP), converseGraph_involutive,
      hcancel,
      value_converseGraph_value hπ.1 hπ.2.1 (hπ.2.2.1.symm ▸ function_value_mem hρ.1 hpP)]

theorem conjugateSubgroup_subgroup {P R Γ π H : V} (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hπ : π ∈ Γ) (hH : IsForcingSubgroup P Γ H) :
    IsForcingSubgroup P Γ (conjugateSubgroup π H) := by
  have ha := hΓ.1 π hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨ρ, hρ, rfl⟩ := (mem_conjugateSubgroup π H θ).mp hθ
    exact hΓ.2.2.1 _ (hΓ.2.2.1 _ (hΓ.2.2.2 π hπ) _ (hH.1 _ hρ)) _ hπ
  · exact (mem_conjugateSubgroup π H _).mpr
      ⟨identity P, hH.2.1, (conjugatePermutation_identity ha).symm⟩
  · intro θ hθ η hη
    obtain ⟨ρ, hρ, rfl⟩ := (mem_conjugateSubgroup π H θ).mp hθ
    obtain ⟨σ, hσ, rfl⟩ := (mem_conjugateSubgroup π H η).mp hη
    exact (mem_conjugateSubgroup π H _).mpr ⟨compose ρ σ, hH.2.2.1 _ hρ _ hσ,
      (conjugatePermutation_compose ha (hΓ.1 _ (hH.1 _ hρ)) (hΓ.1 _ (hH.1 _ hσ))).symm⟩
  · intro θ hθ
    obtain ⟨ρ, hρ, rfl⟩ := (mem_conjugateSubgroup π H θ).mp hθ
    exact (mem_conjugateSubgroup π H _).mpr ⟨converseGraph ρ, hH.2.2.2 _ hρ,
      (conjugatePermutation_inverse ha (hΓ.1 _ (hH.1 _ hρ))).symm⟩

end ZFVP
