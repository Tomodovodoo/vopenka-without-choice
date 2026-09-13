import ZFVP.SetTheory.CohenFiniteAssignmentName
import ZFVP.SetTheory.CohenFixedOrbitName
import ZFVP.SetTheory.SymmetricPairNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The orbit of the pairing of a finite Cohen-real assignment with a supported name. -/
noncomputable def cohenOrbitEvaluationName (E τ : V) : V :=
  cohenFixedOrbitName ∅ {⟨orderedPairName ∅ (cohenFiniteAssignmentName E) τ, (∅ : V)⟩ₖ}

instance cohenFixedOrbitName_definable : ℒₛₑₜ-function₂[V] cohenFixedOrbitName := by
  have h : ℒₛₑₜ-relation₃[V] (fun M C N ↦ ∀ z, z ∈ M ↔
      ∃ b, IsInternalPermutation (ω : V) b ∧ (∀ i ∈ C, b ‘ i = i) ∧
        z ∈ nameAction (cohenPermutation (ω : V) b) N) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenFixedOrbitName (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [cohenFixedOrbitName, mem_sUnion_iff, repl_spec, mem_sep_iff, mem_internalPermutations]
  constructor
  · intro hh z
    rw [hh z]
    constructor
    · rintro ⟨M, ⟨b, ⟨hb, hfix⟩, rfl⟩, hz⟩
      exact ⟨b, hb, hfix, hz⟩
    · rintro ⟨b, hb, hfix, hz⟩
      exact ⟨_, ⟨b, ⟨hb, hfix⟩, rfl⟩, hz⟩
  · intro hh z
    rw [hh z]
    constructor
    · rintro ⟨b, hb, hfix, hz⟩
      exact ⟨_, ⟨b, ⟨hb, hfix⟩, rfl⟩, hz⟩
    · rintro ⟨M, ⟨b, ⟨hb, hfix⟩, rfl⟩, hz⟩
      exact ⟨b, hb, hfix, hz⟩

instance cohenOrbitEvaluationName_definable : ℒₛₑₜ-function₂[V] cohenOrbitEvaluationName := by
  unfold cohenOrbitEvaluationName
  definability

theorem cohenOrbitEvaluationName_base_isName {E τ : V}
    (hEω : E ⊆ (ω : V)) (hτ : IsForcingName (cohenConditions (ω : V)) τ) :
    IsForcingName (cohenConditions (ω : V))
      {⟨orderedPairName ∅ (cohenFiniteAssignmentName E) τ, (∅ : V)⟩ₖ} := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  rw [mem_singleton_iff] at hz
  subst z
  exact ⟨_, ∅, (cohen_top (ω : V)).1, rfl,
    orderedPairName_isName (cohen_top (ω : V)).1 (cohenFiniteAssignmentName_isName hEω) hτ⟩

theorem mem_cohenOrbitEvaluationName {E τ : V}
    (hEω : E ⊆ (ω : V)) (hτ : IsForcingName (cohenConditions (ω : V)) τ) (z : V) :
    z ∈ cohenOrbitEvaluationName E τ ↔
      ∃ b, IsInternalPermutation (ω : V) b ∧
        z = ⟨orderedPairName ∅
          (nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E))
          (nameAction (cohenPermutation (ω : V) b) τ), (∅ : V)⟩ₖ := by
  rw [cohenOrbitEvaluationName, mem_cohenFixedOrbitName (cohenOrbitEvaluationName_base_isName hEω hτ)]
  constructor
  · rintro ⟨b, hb, _, μ, s, hs, hz⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp (mem_singleton_iff.mp hs)
    have htop := forcingAutomorphism_top (cohen_poset (ω : V)) (cohen_top (ω : V))
      (cohenPermutation_automorphism hb)
    rw [nameAction_orderedPairName (cohen_top (ω : V)).1
      (cohenFiniteAssignmentName_isName hEω) hτ, htop] at hz
    exact ⟨b, hb, hz⟩
  · rintro ⟨b, hb, hz⟩
    refine ⟨b, hb, fun _ hi ↦ (not_mem_empty hi).elim, _, ∅, mem_singleton_iff.mpr rfl, ?_⟩
    rw [nameAction_orderedPairName (cohen_top (ω : V)).1
      (cohenFiniteAssignmentName_isName hEω) hτ,
      forcingAutomorphism_top (cohen_poset (ω : V)) (cohen_top (ω : V))
        (cohenPermutation_automorphism hb)]
    exact hz

theorem cohenOrbitEvaluationName_isName {E τ : V}
    (hEω : E ⊆ (ω : V)) (hτ : IsForcingName (cohenConditions (ω : V)) τ) :
    IsForcingName (cohenConditions (ω : V)) (cohenOrbitEvaluationName E τ) :=
  cohenFixedOrbitName_isName (cohenOrbitEvaluationName_base_isName hEω hτ)

theorem cohenOrbitEvaluationName_hereditarilySymmetric {E τ : V}
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ) :
    IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) (cohenOrbitEvaluationName E τ) := by
  apply cohenFixedOrbitName_hereditarilySymmetric (empty_subset _) internallyFinite_empty
    (cohenOrbitEvaluationName_base_isName hEω hτ.1)
  intro μ q hm
  obtain ⟨rfl, _⟩ := kpair_iff.mp (mem_singleton_iff.mp hm)
  exact hereditarilySymmetric_orderedPairName (cohen_poset (ω : V))
    (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V)) (cohen_top (ω : V))
    (cohenFiniteAssignmentName_hereditarilySymmetric hEω hEf) hτ

theorem cohenOrbitEvaluationName_empty_support {E τ : V}
    (hEω : E ⊆ (ω : V)) (hτ : IsForcingName (cohenConditions (ω : V)) τ) :
    IsCohenNameSupport (cohenOrbitEvaluationName E τ) ∅ :=
  ⟨empty_subset _, internallyFinite_empty, fun _ hb hfix ↦
    cohenFixedOrbitName_fixed (empty_subset _) (cohenOrbitEvaluationName_base_isName hEω hτ) hb hfix⟩

end ZFVP

