import ZFVP.SetTheory.NameValueRank
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.BoundedAtomicTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNameValueRowFormula : SetTheorySemisentence 5 :=
  “G T F τ y. (∀ z ∈ y, ∃ σ ∈ T, ∃ p ∈ G,
    !boundedPairMemberFormula τ σ p ∧ !boundedValueFormula z F σ) ∧
    ∀ σ ∈ T, ∀ p ∈ G, !boundedPairMemberFormula τ σ p →
      ∃ z ∈ y, !boundedValueFormula z F σ”

def boundedNameValueTableFormula : SetTheorySemisentence 3 :=
  “G T F. ∀ τ ∈ T, ∃ y ∈ T, !boundedValueFormula y F τ ∧ !boundedNameValueRowFormula G T F τ y”

theorem boundedNameValueRowFormula_bounded : IsBoundedSetFormula boundedNameValueRowFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedValueFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedNameValueTableFormula_bounded : IsBoundedSetFormula boundedNameValueTableFormula :=
  .all (.bvar 1) (.exs (.bvar 2) (.and (boundedValueFormula_bounded.subst _)
    (boundedNameValueRowFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedNameValueRowFormula {G T F τ y : V} [IsTransitive T] (hτ : τ ∈ T) :
    boundedNameValueRowFormula.Evalb ![G, T, F, τ, y] ↔
      ∀ z, z ∈ y ↔ ∃ σ, ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ ∧ z = F ‘ σ := by
  simp [boundedNameValueRowFormula]
  constructor
  · rintro ⟨hl, hr⟩ z
    constructor
    · intro hz
      obtain ⟨σ, _, p, hp, hσp, he⟩ := hl z hz
      exact ⟨σ, p, hp, hσp, he⟩
    · rintro ⟨σ, p, hp, hσp, rfl⟩
      have hσ := (subname_pair_components_mem_transitive hτ hσp).1
      exact hr σ hσ p hp hσp
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨σ, p, hp, hσp, he⟩ := (h z).mp hz
      exact ⟨σ, (subname_pair_components_mem_transitive hτ hσp).1, p, hp, hσp, he⟩
    · intro σ _ p hp hσp
      exact (h _).mpr ⟨σ, p, hp, hσp, rfl⟩

theorem eval_boundedNameValueTableFormula {G T F : V} [IsTransitive T] :
    boundedNameValueTableFormula.Evalb ![G, T, F] ↔
      ∀ τ ∈ T, F ‘ τ ∈ T ∧ ∀ z, z ∈ F ‘ τ ↔
        ∃ σ, ∃ p ∈ G, ⟨σ, p⟩ₖ ∈ τ ∧ z = F ‘ σ := by
  simp (config := { contextual := true }) [boundedNameValueTableFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedNameValueRowFormula]

theorem boundedNameValueTable_unique {G T F : V} [IsTransitive T]
    (hF : boundedNameValueTableFormula.Evalb ![G, T, F]) :
    ∀ τ ∈ T, F ‘ τ = nameValue G τ := by
  have hr := eval_boundedNameValueTableFormula.mp hF
  apply projectedRank_induction T (fun x : V ↦ x) (by definability)
    (fun τ ↦ F ‘ τ = nameValue G τ) (by definability)
  intro τ hτ ih
  apply mem_ext
  intro z
  rw [(hr τ hτ).2, mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, he.trans (ih σ
      (subname_pair_components_mem_transitive hτ hσp).1 (rank_subname_lt hσp))⟩
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, he.trans (ih σ
      (subname_pair_components_mem_transitive hτ hσp).1 (rank_subname_lt hσp)).symm⟩

noncomputable def canonicalNameValueTable (G T : V) : V :=
  definableGraph T (nameValue G) (by definability)

theorem canonicalNameValueTable_value {G T τ : V} (hτ : τ ∈ T) :
    (canonicalNameValueTable G T) ‘ τ = nameValue G τ := value_definableGraph _ _ _ hτ

theorem canonicalNameValueTable_spec {G T : V} [IsTransitive T]
    (hT : ∀ τ ∈ T, nameValue G τ ∈ T) :
    boundedNameValueTableFormula.Evalb ![G, T, canonicalNameValueTable G T] := by
  apply eval_boundedNameValueTableFormula.mpr
  intro τ hτ
  rw [canonicalNameValueTable_value hτ]
  refine ⟨hT τ hτ, ?_⟩
  intro z
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, he.trans (canonicalNameValueTable_value
      (subname_pair_components_mem_transitive hτ hσp).1).symm⟩
  · rintro ⟨σ, p, hp, hσp, he⟩
    exact ⟨σ, p, hp, hσp, he.trans (canonicalNameValueTable_value
      (subname_pair_components_mem_transitive hτ hσp).1)⟩

theorem canonicalNameValueTable_mem_successor {G η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) :
    canonicalNameValueTable G (hierarchy η) ∈ hierarchy (succ η) := by
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨τ, hτ, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz
  exact kpair_mem_hierarchy_limit hη hτ (nameValue_mem_hierarchy hτ)

end ZFVP
