import ZFVP.ModelTheory.SuccessorRankNameDomain
import ZFVP.SetTheory.BoundedAtomicTruth
import ZFVP.SetTheory.NameValueRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedLowNameFamilyFormula : SetTheorySemisentence 3 :=
  “P T N. !isSubsetOf N T ∧ ∀ τ ∈ T, (τ ∈ N ↔
    ∀ z ∈ τ, ∃ σ ∈ N, ∃ p ∈ P, !boundedKpairFormula z σ p)”

theorem boundedLowNameFamilyFormula_bounded : IsBoundedSetFormula boundedLowNameFamilyFormula := by
  repeat' first
    | exact isSubsetOf_bounded.subst _
    | exact boundedKpairFormula_bounded.subst _
    | exact (boundedKpairFormula_bounded.subst _).neg
    | exact IsBoundedSetFormula.rel _ _
    | exact (IsBoundedSetFormula.rel _ _).neg
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedLowNameFamilyFormula {P T N : V} [IsTransitive T] :
    boundedLowNameFamilyFormula.Evalb ![P, T, N] ↔
      N ⊆ T ∧ ∀ τ ∈ T, (τ ∈ N ↔ IsForcingName P τ) := by
  have hev : boundedLowNameFamilyFormula.Evalb ![P, T, N] ↔
      N ⊆ T ∧ ∀ τ ∈ T, (τ ∈ N ↔
        ∀ z ∈ τ, ∃ σ ∈ N, ∃ p ∈ P, z = ⟨σ, p⟩ₖ) := by
    simp [boundedLowNameFamilyFormula]
  rw [hev]
  constructor
  · rintro ⟨hN, hr⟩
    refine ⟨hN, ?_⟩
    apply projectedRank_induction T (fun x : V ↦ x) (by definability)
      (fun τ ↦ τ ∈ N ↔ IsForcingName P τ) (by definability)
    intro τ hτ ih
    rw [hr τ hτ, forcingName_iff]
    constructor
    · intro h z hz
      obtain ⟨σ, hσ, p, hp, he⟩ := h z hz
      have hστ : ⟨σ, p⟩ₖ ∈ τ := he ▸ hz
      exact ⟨σ, p, hp, he, (ih σ (hN σ hσ) (rank_subname_lt hστ)).mp hσ⟩
    · intro h z hz
      obtain ⟨σ, p, hp, he, hσ⟩ := h z hz
      have hστ : ⟨σ, p⟩ₖ ∈ τ := he ▸ hz
      exact ⟨σ, (ih σ (subname_pair_components_mem_transitive hτ hστ).1
        (rank_subname_lt hστ)).mpr hσ, p, hp, he⟩
  · rintro ⟨hN, hr⟩
    refine ⟨hN, fun τ hτ ↦ ?_⟩
    rw [hr τ hτ, forcingName_iff]
    constructor
    · intro h z hz
      obtain ⟨σ, p, hp, he, hσ⟩ := h z hz
      exact ⟨σ, (hr σ (subname_pair_components_mem_transitive hτ (he ▸ hz)).1).mpr hσ,
        p, hp, he⟩
    · intro h z hz
      obtain ⟨σ, hσ, p, hp, he⟩ := h z hz
      exact ⟨σ, p, hp, he, (hr σ (hN σ hσ)).mp hσ⟩

theorem boundedLowNameFamily_rank_iff {P η N : V} [IsOrdinal η] :
    boundedLowNameFamilyFormula.Evalb ![P, hierarchy η, N] ↔ N = lowRankNameSet P η := by
  let := hierarchy_transitive η
  rw [eval_boundedLowNameFamilyFormula]
  constructor
  · rintro ⟨hN, hr⟩
    apply mem_ext
    intro τ
    rw [mem_lowRankNameSet]
    exact ⟨fun h ↦ ⟨hN τ h, (hr τ (hN τ h)).mp h⟩,
      fun ⟨hτ, h⟩ ↦ (hr τ hτ).mpr h⟩
  · rintro rfl
    exact ⟨lowRankNameSet_subset P η, fun τ hτ ↦ by
      rw [mem_lowRankNameSet, and_iff_right hτ]⟩

end ZFVP
