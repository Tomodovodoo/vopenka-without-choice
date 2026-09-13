import ZFVP.SetTheory.PiWitnessRankStages
import ZFVP.ModelTheory.DeltaOneIndexedMarkerStructures
import ZFVP.ModelTheory.LimitRankRestriction

/-! The eight distinguished constants of the fragment construction and their rank structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def piWitnessStructure (ρ α ν U W X c θ d : V) : V :=
  indexedMarkerStructure (hierarchy ρ) (8 : V) (hierarchy (ordinalAdd θ ω))
    (standardTuple ![α, ν, U, W, X, c, θ, d])

@[simp] theorem piWitnessStructure_domain (ρ α ν U W X c θ d : V) :
    structureDomain (piWitnessStructure ρ α ν U W X c θ d) = hierarchy (ordinalAdd θ ω) :=
  indexedMarkerStructure_domain _ _ _ _

def IsPiWitnessRankStructure {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2))
    (ρ M : V) (v : Fin n → V) : Prop :=
  ∃ α ν U W X c θ d : V,
    IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v ∧
      M = piWitnessStructure ρ α ν U W X c θ d

theorem IsPiWitnessRankStage.structure_expansion {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    {ρ α ν U W X c θ d : V} [IsOrdinal ρ] {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v) :
    IsMembershipExpansion (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (8 : V)))
      (piWitnessStructure ρ α ν U W X c θ d) := by
  let := h.rankCriterion.1
  have hρθ := h.bounds.1
  have hρδ := IsOrdinal.toIsTransitive.mem_trans hρθ (ordinalAdd_omega_gt θ)
  have hA : IsNonempty (hierarchy (ordinalAdd θ ω)) := ⟨θ, ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt θ)⟩
  exact indexedMarkerStructure_expansion hA
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hρδ))
    (standardTuple_mem_function _ h.marker_values_mem)

theorem IsPiWitnessRankStructure.valid {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    {ρ M : V} [IsOrdinal ρ] {v : Fin n → V} (h : IsPiWitnessRankStructure k ψ ρ M v) :
    IsStructureCode (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (8 : V))) M := by
  obtain ⟨α, ν, U, W, X, c, θ, d, h, rfl⟩ := h
  exact h.structure_expansion.2.1

theorem piWitnessRankStructure_proper {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (k + 1) φ → VopenkaInstance (V := V) φ)
    (ρ : V) [IsOrdinal ρ] (v : Fin n → V)
    (hu : ∀ δ : V, IsOrdinal δ → ∃ α τ : V, IsOrdinal α ∧ δ ∈ α ∧ ψ.Evalb (τ :> α :> v)) :
    IsProperClass (fun M ↦ IsPiWitnessRankStructure k ψ ρ M v) := by
  intro C
  obtain ⟨α, τ, hα, hCα, hτ⟩ := hu (rank C) inferInstance
  let := hα
  obtain ⟨e, θ, d, h⟩ := piWitnessRankStage_exists hψ hVP ρ α v ⟨τ, hτ⟩
  obtain ⟨ν, U, W, X, a, b, rfl, _⟩ := (eval_piWitnessFamilyCodeFormula ψ e (α :> v)).mp h.2.1
  let := h.rankCriterion.1
  refine ⟨piWitnessStructure ρ α ν U W X ⟨a, b⟩ₖ θ d,
    ⟨α, ν, U, W, X, ⟨a, b⟩ₖ, θ, d, h, rfl⟩, ?_⟩
  intro hm
  have hM := subset_hierarchy_rank C _ hm
  let := hierarchy_transitive (rank C)
  have hA : hierarchy (ordinalAdd θ ω) ∈ hierarchy (rank C) := (kpair_components_mem_transitive hM).1
  have hδC : ordinalAdd θ ω ∈ rank C := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem _ _).mp hA
  have hCθ := IsOrdinal.toIsTransitive.mem_trans hCα h.bounds.2.1
  have hCδ := IsOrdinal.toIsTransitive.mem_trans hCθ (ordinalAdd_omega_gt θ)
  exact mem_irrefl (ordinalAdd θ ω) (IsOrdinal.toIsTransitive.mem_trans hδC hCδ)

theorem IsPiWitnessRankStage.structure_unique {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) {ρ α ν U W X c θ d ν' U' W' X' c' θ' d' : V} {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v)
    (h' : IsPiWitnessRankStage k ψ ρ α ⟨ν', ⟨U', ⟨W', ⟨X', c'⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ' d' v) :
    piWitnessStructure ρ α ν U W X c θ d = piWitnessStructure ρ α ν' U' W' X' c' θ' d' := by
  obtain ⟨he, rfl, rfl⟩ := h.unique hψ h'
  obtain ⟨rfl, he₁⟩ := kpair_inj he
  obtain ⟨rfl, he₂⟩ := kpair_inj he₁
  obtain ⟨rfl, he₃⟩ := kpair_inj he₂
  obtain ⟨rfl, rfl⟩ := kpair_inj he₃
  rfl

end ZFVP
