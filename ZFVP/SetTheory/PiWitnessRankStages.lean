import ZFVP.SetTheory.PiWitnessFamilyCode
import ZFVP.SetTheory.RankWitnessStructures
import ZFVP.SetTheory.PiVopenkaZFRanks
import ZFVP.SetTheory.RankCriterionCodeBounds

/-! The canonical outer rank used for the fragment witness structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsPiWitnessRankStage {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2))
    (ρ α e θ d : V) (v : Fin n → V) : Prop :=
  IsOrdinal α ∧ (piWitnessFamilyCodeFormula k ψ).Evalb (e :> α :> v) ∧
    leastRankCriterionCertificateFormula.Evalb ![θ, d, witnessRankBound ρ α e]

theorem piWitnessRankStage_exists {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (k + 1) φ → VopenkaInstance (V := V) φ)
    (ρ α : V) [IsOrdinal ρ] [IsOrdinal α] (v : Fin n → V)
    (hex : ∃ τ : V, ψ.Evalb (τ :> α :> v)) :
    ∃ e θ d : V, IsPiWitnessRankStage k ψ ρ α e θ d v := by
  obtain ⟨e, he, _⟩ := piWitnessFamilyCode_existsUnique hψ (α :> v) hex
  obtain ⟨θ, hθ, _⟩ := pi_vopenka_leastRankCriterionAbove_existsUnique (by omega) hVP (witnessRankBound ρ α e)
  obtain ⟨d, hd, _⟩ := leastRankCriterionCertificate_exists hθ
  exact ⟨e, θ, d, inferInstance, he, hd⟩

theorem IsPiWitnessRankStage.unique {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) {ρ α e θ d e' θ' d' : V} {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α e θ d v)
    (h' : IsPiWitnessRankStage k ψ ρ α e' θ' d' v) : e = e' ∧ θ = θ' ∧ d = d' := by
  have he := piWitnessFamilyCode_unique hψ (α :> v) h.2.1 h'.2.1
  subst e'
  have hθ := (leastRankCriterionCertificate_sound h.2.2).unique (leastRankCriterionCertificate_sound h'.2.2)
  subst θ'
  have hd := (leastRankCriterionCertificate_exists (leastRankCriterionCertificate_sound h.2.2)).choose_spec.2
  exact ⟨rfl, rfl, (hd d h.2.2).trans (hd d' h'.2.2).symm⟩

theorem IsPiWitnessRankStage.rankCriterion {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    {ρ α e θ d : V} {v : Fin n → V} (h : IsPiWitnessRankStage k ψ ρ α e θ d v) :
    IsRankCriterionHeight θ := ((eval_leastRankCriterionCertificateFormula _ _ _).mp h.2.2).1

theorem IsPiWitnessRankStage.bounds {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    {ρ α e θ d : V} [IsOrdinal ρ] {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α e θ d v) :
    ρ ∈ θ ∧ α ∈ θ ∧ e ∈ hierarchy θ ∧ d ∈ hierarchy (ordinalAdd θ ω) := by
  let := h.1
  let := h.rankCriterion.1
  have hb := ((eval_leastRankCriterionCertificateFormula _ _ _).mp h.2.2).2.1
  obtain ⟨hρ, hα, he⟩ := witnessRankBound_above ρ α e
  exact ⟨IsOrdinal.toIsTransitive.mem_trans hρ hb, IsOrdinal.toIsTransitive.mem_trans hα hb,
    (mem_hierarchy_iff_rank_mem e θ).mpr (IsOrdinal.toIsTransitive.mem_trans he hb),
    leastRankCriterionCertificate_mem h.2.2⟩

theorem witnessFamilyTuple_components_mem {A ν U W X c : V} [IsTransitive A]
    (he : ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∈ A) : ν ∈ A ∧ U ∈ A ∧ W ∈ A ∧ X ∈ A ∧ c ∈ A := by
  obtain ⟨hν, hU⟩ := kpair_components_mem_transitive he
  obtain ⟨hU, hW⟩ := kpair_components_mem_transitive hU
  obtain ⟨hW, hX⟩ := kpair_components_mem_transitive hW
  obtain ⟨hX, hc⟩ := kpair_components_mem_transitive hX
  exact ⟨hν, hU, hW, hX, hc⟩

theorem IsPiWitnessRankStage.marker_values_mem {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    {ρ α ν U W X c θ d : V} [IsOrdinal ρ] {v : Fin n → V}
    (h : IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v) :
    ∀ i : Fin 8, (![α, ν, U, W, X, c, θ, d] i) ∈ hierarchy (ordinalAdd θ ω) := by
  let := h.rankCriterion.1
  let := hierarchy_transitive θ
  obtain ⟨_, hα, he, hd⟩ := h.bounds
  obtain ⟨hν, hU, hW, hX, hc⟩ := witnessFamilyTuple_components_mem he
  have hsub := hierarchy_mono (IsOrdinal.toIsTransitive.transitive θ (ordinalAdd_omega_gt θ))
  have hα' := hsub α (ordinal_subset_hierarchy θ α hα)
  have hθ := ordinal_subset_hierarchy (ordinalAdd θ ω) θ (ordinalAdd_omega_gt θ)
  simp only [Fin.forall_fin_iff_zero_and_forall_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  exact ⟨hα', hsub _ hν, hsub _ hU, hsub _ hW, hsub _ hX, hsub _ hc, hθ, hd⟩

end ZFVP
