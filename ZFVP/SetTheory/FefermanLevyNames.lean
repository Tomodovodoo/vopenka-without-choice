import ZFVP.SetTheory.FefermanLevyFilter
import ZFVP.SetTheory.HereditarySymmetry
import ZFVP.SetTheory.SymmetricSequenceNames
import ZFVP.SetTheory.SymmetryAction

/-! Hereditarily symmetric names in the Feferman-Levy system: the nice names for reals of
each stage, the name of the set of their values, the name of the sequence of these sets,
and the name of the stage part of the generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The nice names for reals over the stage-`n` forcing. -/
noncomputable def flNames (n : V) : V := flNiceNames (flSequence n)

instance flNames_definable : ℒₛₑₜ-function₁[V] flNames := by
  unfold flNames
  definability

theorem mem_flNames {n τ : V} (hn : n ∈ (ω : V)) : τ ∈ flNames n ↔
    ∀ z ∈ τ, ∃ k ∈ (ω : V), ∃ q ∈ flStage n, z = ⟨checkName ∅ k, q⟩ₖ := by
  rw [flNames, mem_flNiceNames, ← flStage_eq_stageConditions hn]

theorem flName_isName {n τ : V} (hn : n ∈ (ω : V)) (hτ : τ ∈ flNames n) :
    IsForcingName (flConditions V) τ := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨k, hk, q, hq, rfl⟩ := (mem_flNames hn).mp hτ z hz
  exact ⟨checkName ∅ k, q, flStage_subset hn _ hq, rfl, checkName_isName fl_top.1 k⟩

theorem flGroup_top {σ : V} (hσ : σ ∈ flGroup V) : σ ‘ (∅ : V) = ∅ :=
  forcingAutomorphism_top fl_poset fl_top (flGroup_group.1 σ hσ)

theorem flGroup_checkName {σ : V} (hσ : σ ∈ flGroup V) (x : V) :
    nameAction σ (checkName ∅ x) = checkName ∅ x :=
  nameAction_checkName fl_top.1 (flGroup_top hσ) x

/-- The group permutes the nice names of every stage. -/
theorem nameAction_flName {n τ σ : V} (hn : n ∈ (ω : V)) (hτ : τ ∈ flNames n) (hσ : σ ∈ flGroup V) :
    nameAction σ τ ∈ flNames n := by
  obtain ⟨π, hπ, rfl⟩ := (mem_flGroup σ).mp hσ
  have hnω : n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive n hn
  apply (mem_flNames hn).mpr
  intro z hz
  obtain ⟨u, p, hup, rfl⟩ := (mem_nameAction_iff (flName_isName hn hτ) _ z).mp hz
  obtain ⟨k, hk, q, hq, he⟩ := (mem_flNames hn).mp hτ _ hup
  obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
  exact ⟨k, hk, _, flPermutation_stage_mem hnω hπ hq, by rw [flGroup_checkName hσ]⟩

theorem nameAction_flName_fixed {n τ σ : V} (hn : n ∈ (ω : V)) (hτ : τ ∈ flNames n)
    (hσ : σ ∈ pointwiseStabilizer (flGroup V) (flStage n)) : nameAction σ τ = τ := by
  obtain ⟨hσG, hσfix⟩ := (mem_pointwiseStabilizer _ _ _).mp hσ
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, p, hup, rfl⟩ := (mem_nameAction_iff (flName_isName hn hτ) _ z).mp hz
    obtain ⟨k, hk, q, hq, he⟩ := (mem_flNames hn).mp hτ _ hup
    obtain ⟨hu, hp⟩ := kpair_iff.mp he
    rw [hu, hp, flGroup_checkName hσG, hσfix q hq]
    rwa [hu, hp] at hup
  · intro hz
    obtain ⟨k, hk, q, hq, rfl⟩ := (mem_flNames hn).mp hτ z hz
    refine (mem_nameAction_iff (flName_isName hn hτ) _ _).mpr ⟨checkName ∅ k, q, hz, ?_⟩
    rw [flGroup_checkName hσG, hσfix q hq]

theorem flName_hereditarilySymmetric {n τ : V} (hn : n ∈ (ω : V)) (hτ : τ ∈ flNames n) :
    IsHereditarilySymmetricName (flConditions V) (flGroup V) (flFilter V) τ := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨flName_isName hn hτ, ?_⟩, ?_⟩
  · refine (mem_flFilter _).mpr ⟨nameStabilizer_subgroup flGroup_group (flName_isName hn hτ), n, hn, ?_⟩
    intro σ hσ
    exact mem_sep_iff.mpr ⟨((mem_pointwiseStabilizer _ _ _).mp hσ).1, nameAction_flName_fixed hn hτ hσ⟩
  · intro σ p hσp
    obtain ⟨k, _, q, _, he⟩ := (mem_flNames hn).mp hτ _ hσp
    rw [(kpair_iff.mp he).1]
    exact hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top k

/-- The name of the set of reals with a stage-`n` nice name. -/
noncomputable def flStageName (n : V) : V :=
  repl (fun τ ↦ ⟨τ, (∅ : V)⟩ₖ) (by definability) (flNames n)

instance flStageName_definable : ℒₛₑₜ-function₁[V] flStageName := by
  unfold flStageName
  definability

theorem mem_flStageName (n z : V) : z ∈ flStageName n ↔ ∃ τ ∈ flNames n, z = ⟨τ, (∅ : V)⟩ₖ := repl_spec _

theorem flStageName_isName {n : V} (hn : n ∈ (ω : V)) : IsForcingName (flConditions V) (flStageName n) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨τ, hτ, rfl⟩ := (mem_flStageName n z).mp hz
  exact ⟨τ, ∅, fl_top.1, rfl, flName_isName hn hτ⟩

theorem nameAction_flStageName {n σ : V} (hn : n ∈ (ω : V)) (hσ : σ ∈ flGroup V) :
    nameAction σ (flStageName n) = flStageName n := by
  have ha := flGroup_group.1 σ hσ
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, p, hup, rfl⟩ := (mem_nameAction_iff (flStageName_isName hn) _ z).mp hz
    obtain ⟨τ, hτ, he⟩ := (mem_flStageName n _).mp hup
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [flGroup_top hσ]
    exact (mem_flStageName n _).mpr ⟨_, nameAction_flName hn hτ hσ, rfl⟩
  · intro hz
    obtain ⟨τ, hτ, rfl⟩ := (mem_flStageName n z).mp hz
    have hinv : converseGraph σ ∈ flGroup V := flGroup_group.2.2.2 σ hσ
    refine (mem_nameAction_iff (flStageName_isName hn) _ _).mpr
      ⟨nameAction (converseGraph σ) τ, ∅,
        (mem_flStageName n _).mpr ⟨_, nameAction_flName hn hτ hinv, rfl⟩, ?_⟩
    rw [nameAction_cancel_inverse ha (flName_isName hn hτ), flGroup_top hσ]

theorem flStageName_hereditarilySymmetric {n : V} (hn : n ∈ (ω : V)) :
    IsHereditarilySymmetricName (flConditions V) (flGroup V) (flFilter V) (flStageName n) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨flStageName_isName hn, ?_⟩, ?_⟩
  · have he : nameStabilizer (flGroup V) (flStageName n) = flGroup V := by
      ext σ
      simp only [nameStabilizer, mem_sep_iff]
      exact ⟨And.left, fun hσ ↦ ⟨hσ, nameAction_flStageName hn hσ⟩⟩
    rw [he]
    exact flFilter_normal.2.1
  · intro σ p hσp
    obtain ⟨τ, hτ, he⟩ := (mem_flStageName n _).mp hσp
    rw [(kpair_iff.mp he).1]
    exact flName_hereditarilySymmetric hn hτ

/-- The sequence of stage names and the name of the sequence of stage sets. -/
noncomputable def flStageSequence (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  definableGraph (ω : V) flStageName (by definability)

noncomputable def flSequenceName (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  sequenceName ∅ (flStageSequence V)

theorem domain_flStageSequence : domain (flStageSequence V) = ω := domain_definableGraph _ _ _

theorem flStageSequence_value {n : V} (hn : n ∈ (ω : V)) : (flStageSequence V) ‘ n = flStageName n :=
  value_definableGraph _ _ _ hn

theorem flSequenceName_hereditarilySymmetric :
    IsHereditarilySymmetricName (flConditions V) (flGroup V) (flFilter V) (flSequenceName V) := by
  apply hereditarilySymmetric_sequenceName fl_poset flGroup_group flFilter_normal fl_top
  · intro i hi
    rw [domain_flStageSequence] at hi
    rw [flStageSequence_value hi]
    exact flStageName_hereditarilySymmetric hi
  · refine ⟨flGroup V, flFilter_normal.2.1, fun σ hσ i hi ↦ ?_⟩
    rw [domain_flStageSequence] at hi
    rw [flStageSequence_value hi]
    exact nameAction_flStageName hi hσ

/-- The name of the stage-`n` part of the generic filter. -/
noncomputable def flGenericName (n : V) : V :=
  repl (fun q ↦ ⟨checkName ∅ q, q⟩ₖ) (by definability) (flStage n)

theorem mem_flGenericName (n z : V) : z ∈ flGenericName n ↔ ∃ q ∈ flStage n, z = ⟨checkName ∅ q, q⟩ₖ :=
  repl_spec _

theorem flGenericName_isName {n : V} (hn : n ∈ (ω : V)) :
    IsForcingName (flConditions V) (flGenericName n) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨q, hq, rfl⟩ := (mem_flGenericName n z).mp hz
  exact ⟨checkName ∅ q, q, flStage_subset hn _ hq, rfl, checkName_isName fl_top.1 q⟩

theorem nameAction_flGenericName_fixed {n σ : V} (hn : n ∈ (ω : V))
    (hσ : σ ∈ pointwiseStabilizer (flGroup V) (flStage n)) :
    nameAction σ (flGenericName n) = flGenericName n := by
  obtain ⟨hσG, hσfix⟩ := (mem_pointwiseStabilizer _ _ _).mp hσ
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, p, hup, rfl⟩ := (mem_nameAction_iff (flGenericName_isName hn) _ z).mp hz
    obtain ⟨q, hq, he⟩ := (mem_flGenericName n _).mp hup
    obtain ⟨hu, hp⟩ := kpair_iff.mp he
    rw [hu, hp, flGroup_checkName hσG, hσfix q hq]
    rwa [hu, hp] at hup
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (mem_flGenericName n z).mp hz
    refine (mem_nameAction_iff (flGenericName_isName hn) _ _).mpr ⟨checkName ∅ q, q, hz, ?_⟩
    rw [flGroup_checkName hσG, hσfix q hq]

theorem flGenericName_hereditarilySymmetric {n : V} (hn : n ∈ (ω : V)) :
    IsHereditarilySymmetricName (flConditions V) (flGroup V) (flFilter V) (flGenericName n) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨flGenericName_isName hn, ?_⟩, ?_⟩
  · refine (mem_flFilter _).mpr ⟨nameStabilizer_subgroup flGroup_group (flGenericName_isName hn), n, hn, ?_⟩
    intro σ hσ
    exact mem_sep_iff.mpr ⟨((mem_pointwiseStabilizer _ _ _).mp hσ).1,
      nameAction_flGenericName_fixed hn hσ⟩
  · intro σ p hσp
    obtain ⟨q, _, he⟩ := (mem_flGenericName n _).mp hσp
    rw [(kpair_iff.mp he).1]
    exact hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top q

end ZFVP
