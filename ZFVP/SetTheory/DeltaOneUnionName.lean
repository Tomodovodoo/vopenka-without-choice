import ZFVP.SetTheory.ForcingUnionName
import ZFVP.SetTheory.NameHierarchyTableFormula
import ZFVP.SetTheory.BoundedAtomicTruth
import ZFVP.Syntax.BoundedTruthClauses

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedUnionNameEntryFormula : SetTheorySemisentence 5 :=
  “T R τ ν q. ∃ σ ∈ T, ∃ s ∈ T, ∃ t ∈ T,
    !boundedPairMemberFormula τ σ s ∧ !boundedPairMemberFormula σ ν t ∧
      !boundedPairMemberFormula R q s ∧ !boundedPairMemberFormula R q t”

def boundedUnionNameGraphFormula : SetTheorySemisentence 5 :=
  “T N P R τ. !boundedSubsetProductFormula N T P ∧
    ∀ ν ∈ T, ∀ q ∈ P,
      !boundedPairMemberFormula N ν q ↔ !boundedUnionNameEntryFormula T R τ ν q”

theorem boundedUnionNameEntryFormula_bounded : IsBoundedSetFormula boundedUnionNameEntryFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem boundedUnionNameGraphFormula_bounded : IsBoundedSetFormula boundedUnionNameGraphFormula :=
  .and (boundedSubsetProductFormula_bounded.subst _)
    (.all (.bvar 0) (.all (.bvar 3) ((boundedPairMemberFormula_bounded.subst _).iff
      (boundedUnionNameEntryFormula_bounded.subst _))))

def sigmaOneUnionNameFormula : SetTheorySemisentence 4 :=
  “N P R τ. ∃ T, !IsTransitive.dfn T ∧ τ ∈ T ∧ !boundedUnionNameGraphFormula T N P R τ”

def piOneUnionNameFormula : SetTheorySemisentence 4 :=
  “N P R τ. ∀ T, !IsTransitive.dfn T → τ ∈ T → !boundedUnionNameGraphFormula T N P R τ”

theorem sigmaOneUnionNameFormula_sigmaOne : IsSigmaFormula 1 sigmaOneUnionNameFormula :=
  .exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.bounded (boundedUnionNameGraphFormula_bounded.subst _))))

theorem piOneUnionNameFormula_piOne : IsPiFormula 1 piOneUnionNameFormula :=
  .all (.or (.bounded (isTransitiveFormula_bounded.subst _).neg)
    (.or (.bounded (.nrel _ _)) (.bounded (boundedUnionNameGraphFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedUnionNameEntryFormula {T τ : V} [IsTransitive T] (hτ : τ ∈ T) (R ν q : V) :
    boundedUnionNameEntryFormula.Evalb ![T, R, τ, ν, q] ↔
      ∃ σ s t : V, ⟨σ, s⟩ₖ ∈ τ ∧ ⟨ν, t⟩ₖ ∈ σ ∧ ⟨q, s⟩ₖ ∈ R ∧ ⟨q, t⟩ₖ ∈ R := by
  have he : boundedUnionNameEntryFormula.Evalb ![T, R, τ, ν, q] ↔
      ∃ σ ∈ T, ∃ s ∈ T, ∃ t ∈ T,
        ⟨σ, s⟩ₖ ∈ τ ∧ ⟨ν, t⟩ₖ ∈ σ ∧ ⟨q, s⟩ₖ ∈ R ∧ ⟨q, t⟩ₖ ∈ R := by
    simp [boundedUnionNameEntryFormula]
  rw [he]
  constructor
  · rintro ⟨σ, _, s, _, t, _, hσ, hν, hs, ht⟩
    exact ⟨σ, s, t, hσ, hν, hs, ht⟩
  · rintro ⟨σ, s, t, hσ, hν, hs, ht⟩
    obtain ⟨hσT, hsT⟩ := subname_pair_components_mem_transitive hτ hσ
    have htT := (subname_pair_components_mem_transitive hσT hν).2
    exact ⟨σ, hσT, s, hsT, t, htT, hσ, hν, hs, ht⟩

theorem forcingUnionName_subset_transitive {T τ : V} [IsTransitive T] (hτ : τ ∈ T) (P R : V) :
    forcingUnionName P R τ ⊆ T ×ˢ P := by
  intro z hz
  obtain ⟨ν, _, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨_, σ, s, t, hσ, hν, _, _⟩ := (mem_forcingUnionName_iff P R τ ν q).mp hz
  have hσT := (subname_pair_components_mem_transitive hτ hσ).1
  exact kpair_mem_iff.mpr ⟨(subname_pair_components_mem_transitive hσT hν).1, hq⟩

theorem eval_boundedUnionNameGraphFormula {T τ : V} [IsTransitive T] (hτ : τ ∈ T) (N P R : V) :
    boundedUnionNameGraphFormula.Evalb ![T, N, P, R, τ] ↔ N = forcingUnionName P R τ := by
  have he : boundedUnionNameGraphFormula.Evalb ![T, N, P, R, τ] ↔
      N ⊆ T ×ˢ P ∧ ∀ ν ∈ T, ∀ q ∈ P,
        (⟨ν, q⟩ₖ ∈ N ↔ ∃ σ s t : V, ⟨σ, s⟩ₖ ∈ τ ∧ ⟨ν, t⟩ₖ ∈ σ ∧ ⟨q, s⟩ₖ ∈ R ∧ ⟨q, t⟩ₖ ∈ R) := by
    simp [boundedUnionNameGraphFormula, eval_boundedSubsetProductFormula,
      eval_boundedUnionNameEntryFormula hτ, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨hsub, h⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨ν, hν, q, hq, rfl⟩ := mem_prod_iff.mp (hsub z hz)
      exact (mem_forcingUnionName_iff P R τ ν q).mpr ⟨hq, (h ν hν q hq).mp hz⟩
    · intro hz
      obtain ⟨ν, hν, q, hq, rfl⟩ := mem_prod_iff.mp (forcingUnionName_subset_transitive hτ P R z hz)
      exact (h ν hν q hq).mpr ((mem_forcingUnionName_iff P R τ ν q).mp hz).2
  · rintro rfl
    exact ⟨forcingUnionName_subset_transitive hτ P R, fun ν _ q hq ↦ by
      simp only [mem_forcingUnionName_iff, hq, true_and]⟩

theorem eval_sigmaOneUnionNameFormula (N P R τ : V) :
    sigmaOneUnionNameFormula.Evalb ![N, P, R, τ] ↔ N = forcingUnionName P R τ := by
  have he : sigmaOneUnionNameFormula.Evalb ![N, P, R, τ] ↔
      ∃ T : V, IsTransitive T ∧ τ ∈ T ∧ boundedUnionNameGraphFormula.Evalb ![T, N, P, R, τ] := by
    simp [sigmaOneUnionNameFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [he]
  constructor
  · rintro ⟨T, hT, hτ, h⟩
    let := hT
    exact (eval_boundedUnionNameGraphFormula hτ N P R).mp h
  · intro h
    let T := transitiveClosure ({τ} : V)
    let : IsTransitive T := transitiveClosure_transitive _
    have hτ : τ ∈ T := subset_transitiveClosure _ _ (by simp)
    exact ⟨T, inferInstance, hτ, (eval_boundedUnionNameGraphFormula hτ N P R).mpr h⟩

theorem eval_piOneUnionNameFormula (N P R τ : V) :
    piOneUnionNameFormula.Evalb ![N, P, R, τ] ↔ N = forcingUnionName P R τ := by
  have he : piOneUnionNameFormula.Evalb ![N, P, R, τ] ↔
      ∀ T : V, IsTransitive T → τ ∈ T → boundedUnionNameGraphFormula.Evalb ![T, N, P, R, τ] := by
    simp [piOneUnionNameFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [he]
  constructor
  · intro h
    let T := transitiveClosure ({τ} : V)
    let : IsTransitive T := transitiveClosure_transitive _
    have hτ : τ ∈ T := subset_transitiveClosure _ _ (by simp)
    exact (eval_boundedUnionNameGraphFormula hτ N P R).mp (h T inferInstance hτ)
  · intro h T hT hτ
    let := hT
    exact (eval_boundedUnionNameGraphFormula hτ N P R).mpr h

end ZFVP

