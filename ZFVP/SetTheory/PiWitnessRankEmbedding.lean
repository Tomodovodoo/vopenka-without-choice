import ZFVP.SetTheory.PiWitnessRankClass

/-! Restricted Vopenka supplies the inner ZF embedding needed for fragment preservation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsPiWitnessRankStage.leastRankWitnessSet {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) {ρ α ν U W X c θ d : V} {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v) :
    IsLeastRankWitnessSet (fun a τ ↦ ψ.Evalb (τ :> a :> v)) α X := by
  obtain ⟨ν', U', W', X', a, b, he, hc⟩ :=
    (eval_piWitnessFamilyCodeFormula ψ _ (α :> v)).mp h.2.1
  obtain ⟨rfl, he₁⟩ := kpair_inj he
  obtain ⟨rfl, he₂⟩ := kpair_inj he₁
  obtain ⟨rfl, he₃⟩ := kpair_inj he₂
  obtain ⟨rfl, _⟩ := kpair_inj he₃
  have ht := ((eval_piWitnessCertificateFormula hψ _ _ _ _ a b (α :> v)).mp hc).1
  exact ⟨ν, ht.least_rank, ht.members⟩

theorem pi_vopenka_witnessRank_embedding {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (k + 1) φ → VopenkaInstance (V := V) φ)
    (ρ : V) [IsOrdinal ρ] (v : Fin n → V)
    (hu : ∀ δ : V, IsOrdinal δ → ∃ α τ : V, IsOrdinal α ∧ δ ∈ α ∧ ψ.Evalb (τ :> α :> v)) :
    ∃ α β X Y θ η f : V,
      α ≠ β ∧ IsRankCriterionHeight θ ∧ IsRankCriterionHeight η ∧ ρ ∈ θ ∧ ρ ∈ η ∧
      IsLeastRankWitnessSet (fun a τ ↦ ψ.Evalb (τ :> a :> v)) α X ∧
      IsLeastRankWitnessSet (fun a τ ↦ ψ.Evalb (τ :> a :> v)) β Y ∧
      X ∈ hierarchy θ ∧ Y ∈ hierarchy η ∧
      IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
      f ‘ α = β ∧ f ‘ X = Y ∧ ∀ i ∈ hierarchy ρ, f ‘ i = i := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class (by omega) hVP
    (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (8 : V)))
    (fun M ↦ IsPiWitnessRankStructure k ψ ρ M v) (piWitnessRankClassFormula k ψ)
    (piWitnessRankClassFormula_pi hψ) (ρ :> hierarchy ρ :> v)
    (fun M ↦ eval_piWitnessRankClassFormula ψ M ρ v)
    (piWitnessRankStructure_proper hψ hVP ρ v hu) (fun _ h ↦ h.valid)
  obtain ⟨α, ν, U, W, X, c, θ, d, h, rfl⟩ := hM
  obtain ⟨β, ν', U', W', Y, c', η, d', h', rfl⟩ := hN
  let := h.rankCriterion.1
  let := h'.rankCriterion.1
  let := h.1
  let := hierarchy_transitive ρ
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hρδ := IsOrdinal.toIsTransitive.mem_trans h.bounds.1 (ordinalAdd_omega_gt θ)
  have hBA := hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hρδ)
  have hv := hf.indexedMarker_values hBA (standardTuple_mem_function _ h.marker_values_mem)
  have hmarks (i : Fin 8) :
      f ‘ (![α, ν, U, W, X, c, θ, d] i) = ![β, ν', U', W', Y, c', η, d'] i := by
    simpa only [value_standardTuple] using hv.1 (i.val : V) (natCast_mem_of_lt i.isLt)
  have houter : IsCodedMembershipEmbedding (hierarchy (ordinalAdd θ ω)) (hierarchy (ordinalAdd η ω)) f := by
    simpa only [piWitnessStructure_domain] using hf.membership_reduct h.structure_expansion h'.structure_expansion
  have hinner := rankCriterionEmbedding_restrict h.rankCriterion houter (hmarks 6)
  have hXθ := (witnessFamilyTuple_components_mem h.bounds.2.2.1).2.2.2.1
  have hYη := (witnessFamilyTuple_components_mem h'.bounds.2.2.1).2.2.2.1
  let := IsFunction.of_mem houter.function
  have hsub := hierarchy_mono (IsOrdinal.toIsTransitive.transitive θ (ordinalAdd_omega_gt θ))
  have hrestrict (x : V) (hx : x ∈ hierarchy θ) : (f ↾ (hierarchy θ)) ‘ x = f ‘ x :=
    value_restrict (by rw [domain_eq_of_mem_function houter.function]; exact hsub x hx) hx
  refine ⟨α, β, X, Y, θ, η, f ↾ (hierarchy θ), ?_, h.rankCriterion, h'.rankCriterion,
    h.bounds.1, h'.bounds.1, h.leastRankWitnessSet hψ, h'.leastRankWitnessSet hψ, hXθ, hYη, hinner, ?_, ?_, ?_⟩
  · intro he
    subst β
    exact hne (h.structure_unique hψ h')
  · rw [hrestrict α (ordinal_subset_hierarchy θ α h.bounds.2.1)]
    exact hmarks 0
  · rw [hrestrict X hXθ]
    exact hmarks 4
  · intro i hi
    have hiθ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ h.bounds.1) i hi
    rw [hrestrict i hiθ]
    exact hv.2 i hi

end ZFVP
