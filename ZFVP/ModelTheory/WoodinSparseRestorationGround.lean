import ZFVP.ModelTheory.PrunedUEWoodinBounds
import ZFVP.ModelTheory.WoodinSparseRestorationLevels
import ZFVP.ModelTheory.FiniteRestorationReflection
import ZFVP.SetTheory.BoundedOrdinalOmega

/-! Ground selection for the actual complete sparse iteration code.
The UE hypotheses come from the pruned theory. The forcing window level and
the parameter-free complete-code formula remain explicit inputs.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] woodinSparseReflectionLevel woodinSparseWitnessBase
  woodinSparseWitnessLevel woodinSparseRestorationBase woodinSparseRestorationLevel

/-- Positive correctness closes the stage under the finite rank buffer. -/
theorem Cn.ordinalAdd_omega_mem {k : ℕ} {Λ θ : V}
    (hΛ : Cn (k + 1) Λ) (hθ : θ ∈ Λ) : ordinalAdd θ (ω : V) ∈ Λ := by
  let := hΛ.ordinal
  let := IsOrdinal.of_mem hθ
  let := hierarchy_transitive (V := V) Λ
  have hθV := ordinal_subset_hierarchy Λ θ hθ
  have hex : ∃ x : V, boundedOrdinalOmegaFormula.Evalb (x :> ![θ]) :=
    ⟨ordinalAdd θ (ω : V), (eval_boundedOrdinalOmegaFormula _ _).mpr ⟨inferInstance, rfl⟩⟩
  obtain ⟨x, hx, hev⟩ := hΛ.2.bounded_witness boundedOrdinalOmegaFormula_bounded ![θ]
    (fun i ↦ by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simpa using hθV) hex
  obtain ⟨_, rfl⟩ := (eval_boundedOrdinalOmegaFormula _ _).mp hev
  exact ordinal_mem_hierarchy_iff.mp hx

variable {r : ℕ} {code : SetTheorySemisentence 2}

theorem woodinSparse_witnessFacts {θ : V}
    (hθ : IsCnExtendible (woodinSparseWitnessLevel r code) θ) :
    Cn r θ ∧ IsWoodinSupercompact θ := by
  have hθ' : IsCnExtendible (woodinSparseWitnessBase r code + 1 + 1) θ := by
    simpa only [woodinSparseWitnessLevel] using hθ
  have hr := woodinSparseWindowLevel_le_base (r := r) (code := code)
  have hW := woodinSparseWoodinComplexity_le_base (r := r) (code := code)
  exact ⟨hθ'.cn.of_le (by omega), IsCnExtendible.woodinSupercompact (hθ'.of_le (by omega))⟩

theorem woodinSparse_restorationFacts {Λ : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ) :
    Cn (woodinSparseRestorationBase r code + 1) Λ ∧ Cn r Λ ∧ IsWoodinSupercompact Λ := by
  have hΛ' : IsCnExtendible (woodinSparseRestorationBase r code + 3 + 1) Λ := by
    simpa only [woodinSparseRestorationLevel] using hΛ
  have hS := woodinSparseWitnessLevel_le_restorationBase (r := r) (code := code)
  rw [woodinSparseWitnessLevel] at hS
  have hr := woodinSparseWindowLevel_le_base (r := r) (code := code)
  have hW := woodinSparseWoodinComplexity_le_base (r := r) (code := code)
  exact ⟨hΛ'.cn.of_le (by omega), hΛ'.cn.of_le (by omega),
    IsCnExtendible.woodinSupercompact (hΛ'.of_le (by omega))⟩

variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

theorem prunedUE_exists_sparseRestorationEndpoint (α : V) (hα : IsOrdinal α) :
    ∃ Λ : V, α ∈ Λ ∧ IsCnExtendible (woodinSparseRestorationLevel r code) Λ ∧
      Cn (woodinSparseRestorationBase r code + 1) Λ ∧ Cn r Λ ∧ IsWoodinSupercompact Λ := by
  obtain ⟨Λ, hαΛ, hΛ⟩ :=
    prunedUE_cnExtendible_unbounded (V := V) (woodinSparseRestorationBase r code + 3) α hα
  have hΛ' : IsCnExtendible (woodinSparseRestorationLevel r code) Λ := by
    simpa only [woodinSparseRestorationLevel] using hΛ
  exact ⟨Λ, hαΛ, hΛ', woodinSparse_restorationFacts hΛ'⟩

/-- Actual `E_s` witnesses occur below the chosen endpoint. Correctness is
used both to find a witness and to identify its ambient extendibility. -/
theorem prunedUE_sparseWitness_below {Λ η : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ) (hη : η ∈ Λ) :
    ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible (woodinSparseWitnessLevel r code) δ := by
  apply exists_cnExtendible_mem_of_cn (woodinSparse_restorationFacts hΛ).1
    woodinSparseExtendibleFormula_sigma ?_ hη
  intro α hα
  simpa only [woodinSparseWitnessLevel] using
    prunedUE_cnExtendible_unbounded (V := V) (woodinSparseWitnessBase r code + 1) α hα

omit [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory] in
theorem woodinSparseReflectionRank_below {Λ η : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ) (hη : η ∈ Λ) :
    ∃ ρ : V, ρ ∈ Λ ∧ η ∈ ρ ∧ Cn (woodinSparseReflectionLevel r code) ρ :=
  exists_cn_mem_of_cn (woodinSparse_restorationFacts hΛ).1 woodinSparseCnFormula_sigma hη

/-- Choose a higher actual witness above two prescribed ordinals of the endpoint. -/
theorem prunedUE_sparseWitness_below_above_two {Λ δ β : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ)
    (hδ : δ ∈ Λ) (hβ : β ∈ Λ) :
    ∃ θ : V, θ ∈ Λ ∧ δ ∈ θ ∧ β ∈ θ ∧ IsCnExtendible (woodinSparseWitnessLevel r code) θ := by
  let := hΛ.1.1
  let := IsOrdinal.of_mem hδ
  let := IsOrdinal.of_mem hβ
  rcases IsOrdinal.mem_trichotomy (α := δ) (β := β) with hlt | heq | hgt
  · obtain ⟨θ, hθΛ, hβθ, hθ⟩ := prunedUE_sparseWitness_below hΛ hβ
    let := hθ.1.1
    exact ⟨θ, hθΛ, IsOrdinal.toIsTransitive.mem_trans hlt hβθ, hβθ, hθ⟩
  · subst β
    obtain ⟨θ, hθΛ, hδθ, hθ⟩ := prunedUE_sparseWitness_below hΛ hδ
    exact ⟨θ, hθΛ, hδθ, hδθ, hθ⟩
  · obtain ⟨θ, hθΛ, hδθ, hθ⟩ := prunedUE_sparseWitness_below hΛ hδ
    let := hθ.1.1
    exact ⟨θ, hθΛ, hδθ, IsOrdinal.toIsTransitive.mem_trans hgt hδθ, hθ⟩

omit [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory] in
/-- Finite reflection at the actual complete code, with its containing correct
rank chosen below the same endpoint. -/
theorem woodinSparseStage_reflects {Λ η δ θ α : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ)
    (hcode : ∀ x γ : V, code.Evalb ![x, γ] ↔ x = woodinSparseCompleteStageCode γ)
    (hAC : ¬InternalChoice V)
    (hδ : IsCnExtendible (woodinSparseWitnessLevel r code) δ)
    (hθ : IsCnExtendible (woodinSparseWitnessLevel r code) θ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθΛ : θ ∈ Λ) (hαθ : α ∈ θ) :
    ∃ ρ : V, ρ ∈ Λ ∧ Cn (woodinSparseReflectionLevel r code) ρ ∧
      Reflects (woodinSparseReflectionLevel r code) (woodinSparseReflectionDictionary r code)
        ![η, δ, θ, ρ, α, woodinSparseCompleteStageCode θ] := by
  have hbuffer := (woodinSparse_restorationFacts hΛ).1.ordinalAdd_omega_mem hθΛ
  obtain ⟨ρ, hρΛ, hθρ, hρ⟩ := woodinSparseReflectionRank_below hΛ hbuffer
  have hδ' : IsCnExtendible (woodinSparseWitnessBase r code + 1 + 1) δ := by
    simpa only [woodinSparseWitnessLevel] using hδ
  have hlevel := woodinSparseReflectionLevel_le_base (r := r) (code := code)
  exact ⟨ρ, hρΛ, hρ,
    finite_reflection_woodinSparseCompleteStageCode code hcode
      woodinSparseReflectionLevel_ge_two woodinSparseDictionary_bound (by omega)
      hδ' hρ hηδ hδθ hθρ hαθ (woodinSparse_witnessFacts hθ).1
      (woodinSparse_witnessFacts hθ).2 hAC⟩

/-- At unboundedly many target stages, every ordinal can be captured by the
actual complete-code ground embedding required by the restricted lift. -/
theorem prunedUE_sparseRestrictedStages {Λ η : V}
    (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ)
    (hcode : ∀ x γ : V, code.Evalb ![x, γ] ↔ x = woodinSparseCompleteStageCode γ)
    (hAC : ¬InternalChoice V) (hη : η ∈ Λ) :
    ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible (woodinSparseWitnessLevel r code) δ ∧
      Cn r δ ∧ IsWoodinSupercompact δ ∧
      ∀ β ∈ Λ, ∃ θ : V, θ ∈ Λ ∧ δ ∈ θ ∧ β ∈ θ ∧ Cn r θ ∧ IsWoodinSupercompact θ ∧
        ∀ α ∈ θ, ∃ e θ' α' J : V,
          η ∈ e ∧ e ∈ θ' ∧ θ' ∈ δ ∧ α' ∈ θ' ∧ Cn r θ' ∧ IsWoodinSupercompact θ' ∧
          IsCodedMembershipEmbedding (hierarchy (ordinalAdd θ' (ω : V)))
            (hierarchy (ordinalAdd θ (ω : V))) J ∧
          IsCriticalPoint (hierarchy (ordinalAdd θ' (ω : V))) J e ∧
          J ‘ e = δ ∧ J ‘ θ' = θ ∧ J ‘ α' = α ∧
          woodinSparseCompleteStageCode θ' ∈ hierarchy (ordinalAdd θ' (ω : V)) ∧
          J ‘ (woodinSparseCompleteStageCode θ') = woodinSparseCompleteStageCode θ := by
  obtain ⟨δ, hδΛ, hηδ, hδ⟩ := prunedUE_sparseWitness_below hΛ hη
  refine ⟨δ, hδΛ, hηδ, hδ, (woodinSparse_witnessFacts hδ).1,
    (woodinSparse_witnessFacts hδ).2, ?_⟩
  intro β hβ
  obtain ⟨θ, hθΛ, hδθ, hβθ, hθ⟩ := prunedUE_sparseWitness_below_above_two hΛ hδΛ hβ
  refine ⟨θ, hθΛ, hδθ, hβθ, (woodinSparse_witnessFacts hθ).1,
    (woodinSparse_witnessFacts hθ).2, ?_⟩
  intro α hαθ
  obtain ⟨ρ, _, hρ, href⟩ := woodinSparseStage_reflects hΛ hcode hAC hδ hθ hηδ hδθ hθΛ hαθ
  exact exists_woodinSparse_restricted_reflection code hcode
    (Nat.le_trans (by decide) woodinSparseReflectionLevel_ge_two) hρ hAC href

end ZFVP
