import ZFVP.SetTheory.CountableSubsetFamily
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.MembershipRecursion
import ZFVP.SetTheory.WellOrderedSurjection

/-! The transfinite selection that builds an omega-Jonsson function.

The construction of an omega-Jonsson function for `lam` runs through a list of demands, one for
each pair `⟨A, γ⟩` with `A ⊆ lam`, `lam ≤# A` and `γ ∈ lam`, and answers each demand with a fresh
countably enumerated subset of `A`. This file sets up the machinery: the set of demands, a
definable enumeration of the demands by an ordinal, the set of still unused answers to a demand,
and the recursion that picks one of them at every stage.

Everything here is stated for arbitrary parameters. The hypotheses that make the recursion do what
it should (the enumeration is onto the demands, the pool of answers never runs out) are supplied in
`ZFVP.SetTheory.OmegaJonssonExistence`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance countableSubsets_definable : ℒₛₑₜ-function₁[V] countableSubsets := by
  have h : ℒₛₑₜ-relation
      (fun Y lam : V ↦ ∀ a, a ∈ Y ↔ ∃ g, g ∈ lam ^ (ω : V) ∧ range g = a) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableSubsets (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countableSubsets_iff]

instance countableSubsetsOf_definable : ℒₛₑₜ-function₂[V] countableSubsetsOf := by
  have h : ℒₛₑₜ-relation₃
      (fun Y lam A : V ↦ ∀ a, a ∈ Y ↔ a ∈ countableSubsets lam ∧ a ⊆ A) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countableSubsetsOf (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countableSubsetsOf_iff]

/-- The demands the construction has to meet: the pairs `⟨A, γ⟩` with `A` a subset of `lam` that
`lam` injects into, and `γ` a point of `lam`. -/
noncomputable def jonssonDemands (lam : V) : V := {q ∈ ℘ lam ×ˢ lam ; lam ≤# kpair.π₁ q}

theorem mem_jonssonDemands_iff {lam q : V} :
    q ∈ jonssonDemands lam ↔ q ∈ ℘ lam ×ˢ lam ∧ lam ≤# kpair.π₁ q := by
  simp only [jonssonDemands, mem_sep_iff]

theorem kpair_mem_jonssonDemands_iff {lam A γ : V} :
    ⟨A, γ⟩ₖ ∈ jonssonDemands lam ↔ A ⊆ lam ∧ γ ∈ lam ∧ lam ≤# A := by
  rw [mem_jonssonDemands_iff, kpair_mem_iff, mem_power_iff, kpair.π₁_kpair, and_assoc]

theorem jonssonDemands_subset {lam : V} : jonssonDemands lam ⊆ ℘ lam ×ˢ lam :=
  fun _ hq ↦ (mem_jonssonDemands_iff.mp hq).1

/-- The demand at stage `ξ`, read off an inverse enumeration `e` of the demand set `D`, with `d₀`
as the value at the stages `e` does not hit. -/
noncomputable def demandAt (D e d₀ ξ : V) : V := by
  classical
  exact if e ‘ ξ ∈ D then e ‘ ξ else d₀

instance demandAt_definable (D e d₀ : V) : ℒₛₑₜ-function₁[V] (demandAt D e d₀) := by
  have h : ℒₛₑₜ-relation (fun y ξ : V ↦ (e ‘ ξ ∈ D ∧ y = e ‘ ξ) ∨ (e ‘ ξ ∉ D ∧ y = d₀)) := by
    definability
  apply Language.Definable.of_iff h
  intro w
  change w 0 = demandAt D e d₀ (w 1) ↔ _
  unfold demandAt
  split <;> simp_all

theorem demandAt_mem {D e d₀ : V} (hd₀ : d₀ ∈ D) (ξ : V) : demandAt D e d₀ ξ ∈ D := by
  unfold demandAt
  split
  · assumption
  · exact hd₀

theorem demandAt_eq_of_mem {D e d₀ ξ : V} (h : e ‘ ξ ∈ D) : demandAt D e d₀ ξ = e ‘ ξ := by
  simp only [demandAt, h, ↓reduceIte]

/-- The answers still available at stage `ξ`: the countably enumerated subsets of the first
coordinate of the demand that the partial selection `pg` has not already used. -/
noncomputable def jonssonCandidates (lam D e d₀ ξ pg : V) : V :=
  {a ∈ countableSubsetsOf lam (kpair.π₁ (demandAt D e d₀ ξ)) ; a ∉ range pg}

theorem mem_jonssonCandidates_iff {lam D e d₀ ξ pg a : V} :
    a ∈ jonssonCandidates lam D e d₀ ξ pg ↔
      a ∈ countableSubsetsOf lam (kpair.π₁ (demandAt D e d₀ ξ)) ∧ a ∉ range pg := by
  simp only [jonssonCandidates, mem_sep_iff]

instance jonssonCandidates_definable (lam D e d₀ : V) :
    ℒₛₑₜ-function₂[V] (jonssonCandidates lam D e d₀) := by
  have h : ℒₛₑₜ-relation₃ (fun Y ξ pg : V ↦ ∀ a, a ∈ Y ↔
      a ∈ countableSubsetsOf lam (kpair.π₁ (demandAt D e d₀ ξ)) ∧ a ∉ range pg) := by
    definability
  apply Language.Definable.of_iff h
  intro w
  change w 0 = jonssonCandidates lam D e d₀ (w 1) (w 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_jonssonCandidates_iff]

/-- One step of the selection: take the available answer with the least value under the injection
`u` of the countably enumerated subsets into an ordinal. -/
noncomputable def jonssonStep (lam D e d₀ u ξ pg : V) : V :=
  wellOrderSelection u (jonssonCandidates lam D e d₀ ξ pg)

instance jonssonStep_definable (lam D e d₀ u : V) :
    ℒₛₑₜ-function₂[V] (jonssonStep lam D e d₀ u) := by
  unfold jonssonStep
  definability

/-- The selection function, defined by recursion on the ordinal `θ` of stages. -/
noncomputable def jonssonSelection (lam D e d₀ u θ : V) : V :=
  wellFoundedRecursion (membershipRelation_wellFounded θ) (jonssonStep lam D e d₀ u) inferInstance

instance jonssonSelection_isFunction (lam D e d₀ u θ : V) :
    IsFunction (jonssonSelection lam D e d₀ u θ) :=
  wellFoundedRecursion_isFunction _ _ _

theorem domain_jonssonSelection (lam D e d₀ u θ : V) :
    domain (jonssonSelection lam D e d₀ u θ) = θ :=
  domain_wellFoundedRecursion _ _ _

theorem jonssonSelection_value {lam D e d₀ u θ ξ : V} [IsOrdinal θ] (hξ : ξ ∈ θ) :
    (jonssonSelection lam D e d₀ u θ) ‘ ξ =
      jonssonStep lam D e d₀ u ξ ((jonssonSelection lam D e d₀ u θ) ↾ ξ) := by
  unfold jonssonSelection
  rw [wellFoundedRecursion_value _ _ _ hξ,
    membershipRelation_predecessors IsOrdinal.toIsTransitive hξ]

/-- The values before stage `ξ` are exactly the range of the restriction to `ξ`. -/
theorem mem_range_restrict_jonssonSelection_iff {lam D e d₀ u θ ξ y : V} [IsOrdinal θ]
    (hξ : ξ ∈ θ) : y ∈ range ((jonssonSelection lam D e d₀ u θ) ↾ ξ) ↔
      ∃ η ∈ ξ, (jonssonSelection lam D e d₀ u θ) ‘ η = y := by
  have hfun := jonssonSelection_isFunction lam D e d₀ u θ
  have hdom := domain_jonssonSelection lam D e d₀ u θ
  constructor
  · intro hy
    obtain ⟨η, hη⟩ := mem_range_iff.mp hy
    obtain ⟨hηf, hηξ⟩ := kpair_mem_restrict_iff.mp hη
    exact ⟨η, hηξ, value_eq_of_kpair_mem hηf⟩
  · rintro ⟨η, hηξ, rfl⟩
    have hηθ : η ∈ domain (jonssonSelection lam D e d₀ u θ) := by
      rw [hdom]
      exact IsOrdinal.toIsTransitive.mem_trans hηξ hξ
    exact mem_range_of_kpair_mem
      (kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hηθ, hηξ⟩)

/-- The pair a stage contributes to the omega-Jonsson function: the selected set, together with
the second coordinate of the demand answered at that stage. -/
instance jonssonEntry_definable (G D e d₀ : V) :
    ℒₛₑₜ-function₁[V] (fun ξ : V ↦ (⟨G ‘ ξ, kpair.π₂ (demandAt D e d₀ ξ)⟩ₖ : V)) := by
  definability

/-- The graph collected from the stages of the selection. -/
noncomputable def jonssonFunction (lam G D e d₀ θ : V) : V :=
  {q ∈ ℘ lam ×ˢ lam ; ∃ ξ ∈ θ, q = ⟨G ‘ ξ, kpair.π₂ (demandAt D e d₀ ξ)⟩ₖ}

theorem mem_jonssonFunction_iff {lam G D e d₀ θ q : V} :
    q ∈ jonssonFunction lam G D e d₀ θ ↔ q ∈ ℘ lam ×ˢ lam ∧
      ∃ ξ ∈ θ, q = ⟨G ‘ ξ, kpair.π₂ (demandAt D e d₀ ξ)⟩ₖ := by
  simp only [jonssonFunction, mem_sep_iff]

theorem jonssonFunction_subset {lam G D e d₀ θ : V} :
    jonssonFunction lam G D e d₀ θ ⊆ ℘ lam ×ˢ lam :=
  fun _ hq ↦ (mem_jonssonFunction_iff.mp hq).1

/-- Restricting an internal function to a subset of its domain gives an internal function from
that subset onto the restricted range. -/
theorem restrict_mem_function {f A : V} (hf : IsFunction f) (hA : A ⊆ domain f) :
    f ↾ A ∈ range (f ↾ A) ^ A := by
  have hres : IsFunction (f ↾ A) :=
    IsFunction.ofSubset f (f ↾ A) (fun p hp ↦ (mem_restrict_iff.mp hp).1)
  have hd : domain (f ↾ A) = A := by
    rw [domain_restrict_eq]
    apply mem_ext
    intro z
    simp only [mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hA z h, h⟩⟩
  have h := IsFunction.mem_function (f ↾ A)
  rwa [hd] at h

end ZFVP
