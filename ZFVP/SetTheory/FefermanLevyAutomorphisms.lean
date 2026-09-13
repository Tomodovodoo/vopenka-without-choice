import ZFVP.SetTheory.FefermanLevyForcing
import ZFVP.SetTheory.PartialFunctionAutomorphisms

/-! Column permutations act on the Feferman-Levy conditions by permuting positions
within each column; the induced maps form an automorphism group, and permutations
fixing the first `n` columns fix every stage-`n` condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem flCondition_finitePartial {p : V} (hp : p ∈ flConditions V) :
    p ∈ finitePartialFunctions (columnCoordinates V) (⋃ˢ repl flCardinal (by definability) (ω : V)) :=
  ((mem_flStage _ _).mp hp).1

theorem flConditions_permutedGraph {π p : V} (hπ : IsColumnPermutation π) (hp : p ∈ flConditions V) :
    permutedGraph π p ∈ flConditions V := by
  have hpf := flCondition_finitePartial hp
  have : IsFunction p := flStage_function hp
  refine (mem_flStage _ _).mpr ⟨permutedGraph_condition hπ.1 hpf, ?_⟩
  intro z hz
  obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p z).mp hz
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
  have hx : x ∈ columnCoordinates V := finitePartialFunction_domain hpf _ (mem_domain_of_kpair_mem hu)
  have hv := flStage_values hp _ hu
  simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair] at hv ⊢
  rwa [hπ.2 x hx]

theorem flStage_permutedGraph {n π p : V} (hn : n ⊆ (ω : V)) (hπ : IsColumnPermutation π)
    (hp : p ∈ flStage n) : permutedGraph π p ∈ flStage n := by
  have hfull := flConditions_permutedGraph hπ (flStage_mono hn _ hp)
  have : IsFunction p := flStage_function hp
  have : IsFunction (permutedGraph π p) := flStage_function hfull
  apply flStage_of_bounds (flStage_finite_domain hfull) ?_ (flStage_values hfull)
  intro w hw
  obtain ⟨y, hwy⟩ := mem_domain_iff.mp hw
  obtain ⟨u, huy, rfl⟩ := (pair_mem_permutedGraph π p w y).mp hwy
  have hu : u ∈ n ×ˢ (ω : V) := flStage_domain hp u (mem_domain_of_kpair_mem huy)
  have huc : u ∈ columnCoordinates V := by
    obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hu
    exact kpair_mem_iff.mpr ⟨hn m hm, hk⟩
  have hπu : π ‘ u ∈ columnCoordinates V := hπ.value_mem huc
  obtain ⟨m', hm', k', hk', he⟩ := mem_prod_iff.mp hπu
  have hcol := hπ.2 u huc
  rw [he] at hcol ⊢
  simp only [kpair.π₁_kpair] at hcol
  obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hu
  simp only [kpair.π₁_kpair] at hcol
  rw [hcol]
  exact kpair_mem_iff.mpr ⟨hm, hk'⟩

noncomputable def flPermutation (π : V) : V :=
  definableGraph (flConditions V) (permutedGraph π) (by definability)

instance flPermutation_definable : ℒₛₑₜ-function₁[V] flPermutation := by
  have h : ℒₛₑₜ-relation[V] (fun f π ↦ ∀ z, z ∈ f ↔
      ∃ p ∈ flConditions V, z = ⟨p, permutedGraph π p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = flPermutation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [flPermutation, mem_definableGraph_iff]

theorem flPermutation_value {π p : V} (hp : p ∈ flConditions V) :
    (flPermutation π) ‘ p = permutedGraph π p := value_definableGraph _ _ _ hp

theorem flPermutation_function {π : V} (hπ : IsColumnPermutation π) :
    flPermutation π ∈ flConditions V ^ flConditions V :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ flConditions_permutedGraph hπ hp)

theorem flPermutation_automorphism {π : V} (hπ : IsColumnPermutation π) :
    IsForcingAutomorphism (flConditions V) (flOrder V) (flPermutation π) := by
  have hf := flPermutation_function hπ
  have : IsFunction (flPermutation π) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    have hpP := (mem_of_mem_functions hf hp).1
    have hqP := (mem_of_mem_functions hf hq).1
    have he : permutedGraph π p = permutedGraph π q := by
      rw [← flPermutation_value hpP, ← flPermutation_value hqP]
      exact (value_eq_of_kpair_mem hp).trans (value_eq_of_kpair_mem hq).symm
    have hh := congrArg (permutedGraph (converseGraph π)) he
    simpa only [permutedGraph_inverse hπ.1 (flCondition_finitePartial hpP),
      permutedGraph_inverse hπ.1 (flCondition_finitePartial hqP)] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hi := flConditions_permutedGraph hπ.inv hq
    have hv : (flPermutation π) ‘ (permutedGraph (converseGraph π) q) = q := by
      rw [flPermutation_value hi, permutedGraph_inverse_right hπ.1 (flCondition_finitePartial hq)]
    exact hv ▸ value_mem_range hf hi
  · intro p hp q hq
    rw [pair_mem_flOrder, pair_mem_flOrder, flPermutation_value hp, flPermutation_value hq]
    have hp' := flConditions_permutedGraph hπ hp
    have hq' := flConditions_permutedGraph hπ hq
    simp only [hp, hq, hp', hq', true_and]
    constructor
    · exact permutedGraph_mono
    · intro h
      have hh := permutedGraph_mono (π := converseGraph π) h
      simpa only [permutedGraph_inverse hπ.1 (flCondition_finitePartial hp),
        permutedGraph_inverse hπ.1 (flCondition_finitePartial hq)] using hh

theorem flPermutation_identity :
    flPermutation (identity (columnCoordinates V)) = identity (flConditions V) := by
  have hf := flPermutation_function (IsColumnPermutation.identity (V := V))
  have : IsFunction (flPermutation (identity (columnCoordinates V))) := IsFunction.of_mem hf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function (identity_mem_function _)]
  · intro p hp
    have hpP : p ∈ flConditions V := domain_eq_of_mem_function hf ▸ hp
    rw [flPermutation_value hpP, permutedGraph_identity (flCondition_finitePartial hpP), identity_value hpP]

theorem flPermutation_compose {π ρ : V} (hπ : IsColumnPermutation π) (hρ : IsColumnPermutation ρ) :
    flPermutation (compose π ρ) = compose (flPermutation π) (flPermutation ρ) := by
  have hf := flPermutation_function hπ
  have hg := flPermutation_function hρ
  have hh := flPermutation_function (hπ.comp hρ)
  have : IsFunction (flPermutation (compose π ρ)) := IsFunction.of_mem hh
  have : IsFunction (compose (flPermutation π) (flPermutation ρ)) :=
    IsFunction.of_mem (compose_function hf hg)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hh, domain_eq_of_mem_function (compose_function hf hg)]
  · intro p hp
    have hpP : p ∈ flConditions V := domain_eq_of_mem_function hh ▸ hp
    rw [flPermutation_value hpP, value_compose_of_mem_function hf hg hpP, flPermutation_value hpP,
      flPermutation_value (flConditions_permutedGraph hπ hpP)]
    exact (permutedGraph_compose hπ.1 hρ.1 (flCondition_finitePartial hpP)).symm

theorem flPermutation_inverse {π : V} (hπ : IsColumnPermutation π) :
    flPermutation (converseGraph π) = converseGraph (flPermutation π) := by
  have ha := flPermutation_automorphism hπ
  have hb := flPermutation_function hπ.inv
  have hc := (forcingAutomorphism_inverse ha).1
  have : IsFunction (flPermutation (converseGraph π)) := IsFunction.of_mem hb
  have : IsFunction (converseGraph (flPermutation π)) := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hb, domain_eq_of_mem_function hc]
  · intro p hp
    have hpP : p ∈ flConditions V := domain_eq_of_mem_function hb ▸ hp
    apply injective_value_eq ha.1 ha.2.1 (function_value_mem hb hpP) (function_value_mem hc hpP)
    rw [flPermutation_value hpP, flPermutation_value (flConditions_permutedGraph hπ.inv hpP),
      permutedGraph_inverse_right hπ.1 (flCondition_finitePartial hpP)]
    exact (value_converseGraph_value ha.1 ha.2.1 (ha.2.2.1.symm ▸ hpP)).symm

noncomputable def flGroup (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  repl flPermutation (by definability) (columnPermutations V)

theorem mem_flGroup (σ : V) : σ ∈ flGroup V ↔ ∃ π, IsColumnPermutation π ∧ σ = flPermutation π := by
  simp only [flGroup, repl_spec, mem_columnPermutations]

theorem flGroup_group : IsForcingAutomorphismGroup (flConditions V) (flOrder V) (flGroup V) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_flGroup σ).mp hσ
    exact flPermutation_automorphism hπ
  · exact (mem_flGroup _).mpr ⟨_, IsColumnPermutation.identity, flPermutation_identity.symm⟩
  · intro σ hσ τ hτ
    obtain ⟨π, hπ, rfl⟩ := (mem_flGroup σ).mp hσ
    obtain ⟨ρ, hρ, rfl⟩ := (mem_flGroup τ).mp hτ
    exact (mem_flGroup _).mpr ⟨compose π ρ, hπ.comp hρ, (flPermutation_compose hπ hρ).symm⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_flGroup σ).mp hσ
    exact (mem_flGroup _).mpr ⟨converseGraph π, hπ.inv, (flPermutation_inverse hπ).symm⟩

/-- A column permutation fixing the first `n` columns fixes every stage-`n` condition. -/
theorem permutedGraph_fixed_of_columns {n π p : V} (hn : n ⊆ (ω : V))
    (hfix : FixesColumnsBelow n π) (hp : p ∈ flStage n) : permutedGraph π p = p := by
  have : IsFunction p := flStage_function hp
  have hval (u : V) (hu : u ∈ domain p) : π ‘ u = u := by
    have hu' : u ∈ n ×ˢ (ω : V) := flStage_domain hp u hu
    obtain ⟨m, hm, k, hk, rfl⟩ := mem_prod_iff.mp hu'
    exact hfix _ (kpair_mem_iff.mpr ⟨hn m hm, hk⟩) (by simpa using hm)
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      hval x (mem_domain_of_kpair_mem hu)] using hu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_permutedGraph π p x y).mpr ⟨x, hz, (hval x (mem_domain_of_kpair_mem hz)).symm⟩

theorem flPermutation_fixed_of_columns {n π p : V} (hn : n ⊆ (ω : V))
    (hfix : FixesColumnsBelow n π) (hp : p ∈ flStage n) : (flPermutation π) ‘ p = p := by
  rw [flPermutation_value (flStage_mono hn _ hp)]
  exact permutedGraph_fixed_of_columns hn hfix hp

/-- Column permutations preserve every stage. -/
theorem flPermutation_stage_mem {n π p : V} (hn : n ⊆ (ω : V)) (hπ : IsColumnPermutation π)
    (hp : p ∈ flStage n) : (flPermutation π) ‘ p ∈ flStage n := by
  rw [flPermutation_value (flStage_mono hn _ hp)]
  exact flStage_permutedGraph hn hπ hp

theorem flGroup_stage_image {n σ : V} (hn : n ⊆ (ω : V)) (hσ : σ ∈ flGroup V) :
    repl (fun p ↦ σ ‘ p) (by definability) (flStage n) = flStage n := by
  obtain ⟨π, hπ, rfl⟩ := (mem_flGroup σ).mp hσ
  apply mem_ext
  intro q
  rw [repl_spec]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact flPermutation_stage_mem hn hπ hp
  · intro hq
    refine ⟨(flPermutation (converseGraph π)) ‘ q, flPermutation_stage_mem hn hπ.inv hq, ?_⟩
    have hqP := flStage_mono hn _ hq
    rw [flPermutation_value hqP, flPermutation_value (flConditions_permutedGraph hπ.inv hqP),
      permutedGraph_inverse_right hπ.1 (flCondition_finitePartial hqP)]

end ZFVP
