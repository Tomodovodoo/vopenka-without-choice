import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.SetTheory.FunctionClosureClub

/-! A club reflecting actual incompatibility witnesses for a maximal compatible family. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def incompatibleMembers (P R F q : V) : V :=
  {u ∈ F ; ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R}

theorem incompatibleMembers_definable (P R F : V) :
    ℒₛₑₜ-function₁[V] (incompatibleMembers P R F) := by
  have hh : ℒₛₑₜ-relation[V] (fun S q ↦ ∀ u, u ∈ S ↔ u ∈ F ∧
    ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [incompatibleMembers, mem_sep_iff]
  rfl

noncomputable def incompatibilityWitness (P R F q : V) : V := by
  classical
  exact if IsNonempty (incompatibleMembers P R F q) then ⋂ˢ incompatibleMembers P R F q else q

theorem incompatibilityWitness_definable (P R F : V) :
    ℒₛₑₜ-function₁[V] (incompatibilityWitness P R F) := by
  have := incompatibleMembers_definable P R F
  have hh : ℒₛₑₜ-relation[V] (fun u q ↦
      (IsNonempty (incompatibleMembers P R F q) ∧ u = ⋂ˢ incompatibleMembers P R F q) ∨
      (¬IsNonempty (incompatibleMembers P R F q) ∧ u = q)) := by definability
  apply Language.Definable.of_iff hh
  intro v
  simp only [incompatibilityWitness]
  split_ifs <;> simp_all

theorem incompatibilityWitness_mem {κ P R F q : V} [IsOrdinal κ]
    (hFP : F ⊆ P) (hP : P ⊆ κ) (hq : q ∈ κ) :
    incompatibilityWitness P R F q ∈ κ := by
  classical
  unfold incompatibilityWitness
  split_ifs with h
  · have := h
    have hu := IsOrdinal.sInter_mem (X := incompatibleMembers P R F q)
      (fun u hu ↦ IsOrdinal.of_mem (hP u (hFP u (mem_sep_iff.mp hu).1)))
    exact hP _ (hFP _ (mem_sep_iff.mp hu).1)
  · exact hq

theorem incompatibilityWitness_spec {κ P R F q : V} [IsOrdinal κ]
    (hF : IsInternalMaximallyCompatible P R F) (hP : P ⊆ κ)
    (hq : q ∈ P) (hqF : q ∉ F) :
    incompatibilityWitness P R F q ∈ F ∧
      ¬∃ z ∈ P, ⟨incompatibilityWitness P R F q, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R := by
  classical
  have hne : IsNonempty (incompatibleMembers P R F q) := by
    have hex : ∃ u ∈ F, ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R := by
      by_contra h
      apply hqF
      apply hF.2.2 q hq
      push Not at h
      exact h
    obtain ⟨u, hu, hb⟩ := hex
    exact ⟨u, mem_sep_iff.mpr ⟨hu, hb⟩⟩
  have hu := IsOrdinal.sInter_mem (X := incompatibleMembers P R F q)
    (fun u hu ↦ IsOrdinal.of_mem (hP u (hF.1 u (mem_sep_iff.mp hu).1)))
  simpa only [incompatibilityWitness, ite_eq_left hne] using (mem_sep_iff.mp hu)

theorem exists_hartogsOmega_incompatibilityClub (hAC : InternalChoice V) {P R F : V}
    (hF : IsInternalMaximallyCompatible P R F) (hP : P ⊆ hartogsNumber (ω : V)) :
    ∃ E : V, IsClubIn E (hartogsNumber (ω : V)) ∧ ∀ α ∈ E,
      IsLimitOrdinal α ∧ ∀ q ∈ α, q ∈ P → q ∉ F → ∃ u ∈ F ∩ α,
        ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R := by
  let κ := hartogsNumber (ω : V)
  let g := definableGraph κ (incompatibilityWitness P R F) (incompatibilityWitness_definable P R F)
  have hg : g ∈ κ ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun q hq ↦ incompatibilityWitness_mem hF.1 hP hq)
  refine ⟨functionClosureClub κ g, hartogsOmega_functionClosureClub hAC hg, fun α hα ↦ ?_⟩
  obtain ⟨_, hlim, hclosed⟩ := (mem_functionClosureClub _ _ _).mp hα
  refine ⟨hlim, fun q hq hqP hqF ↦ ?_⟩
  have hqκ : q ∈ κ := hP q hqP
  have hu := incompatibilityWitness_spec hF hP hqP hqF
  refine ⟨incompatibilityWitness P R F q, mem_inter_iff.mpr ⟨hu.1, ?_⟩, hu.2⟩
  simpa only [g, value_definableGraph _ _ _ hqκ] using hclosed q hq

end ZFVP.Schmerl
