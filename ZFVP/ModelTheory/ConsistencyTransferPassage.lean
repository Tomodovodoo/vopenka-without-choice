import ZFVP.SetTheory.EffectiveFiniteLanguageReduction
import ZFVP.ModelTheory.TheoryCompactness
import ZFVP.ModelTheory.CountablePrunedGroundModel
import ZFVP.ModelTheory.SVCVopenkaRestoration

/-! # Theorem B: `Con(ZF+VP) ↔ Con(ZFC+VP)`

This file assembles the compactness half of the paper's `thm:consistency-transfer`, together
with the converse and the resulting equivalence.

What the syntactic passage means here. A finite subset `F` of `ZFC+VP` is a
`Finset (Sentence ℒₛₑₜ)` whose coercion to a `Theory ℒₛₑₜ` is included in `zfcVPTheory`;
"`W` models `F`" is `W↓[ℒₛₑₜ] ⊧* (F : Theory ℒₛₑₜ)` for a type `W` carrying an arbitrary
`SetStructure`, that is, an arbitrary membership relation on `W`. Nothing asks that relation
to be well founded, nor that `W` be transitive or an initial segment of anything, so the
models in play here may be ill founded. Consistency is Foundation's `Entailment.Consistent`
on the theory, a statement about derivations. The step from "every finite subset has a
model" to "the theory is consistent" is `consistent_of_finite_subsets_satisfiable`, whose
proof is the finite-axiom property of the sequent calculus plus soundness; no ultraproduct
and no choice principle in the metatheory beyond `Classical.choice` is involved.

The paper's `thm:finite-restoration` enters this compactness argument as the explicit
hypothesis `FiniteRestorationInput`. `WoodinSparseRestorationTheorem` proves that input
from the actual forcing construction and obtains the closed consistency equivalence.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- The finite restoration input, in exactly the form the proof of Theorem B consumes.

From a countable model `M` of `ZF+VP+UE+"there are no rank-Berkeley cardinals"` in which
Choice fails, and a level `N ≥ 1`, one gets a model `W` of `ZFC` with a proper class of
`C(N)`-extendible cardinals.

In the paper `W` is the rank `(M[H])_Λ` of a generic extension of `M`, produced by
`thm:finite-restoration` (node W09 of the formalization). The compactness
argument below uses nothing about where `W` comes from: not that it is countable, not that
it extends `M`, not anything about `Λ` or the forcing. So this definition records only what
is used; `ZFVP.finite_restoration` supplies it from the actual sparse endpoint. -/
def FiniteRestorationInput : Prop :=
  ∀ (M : Type) (_ : SetStructure M) (_ : Nonempty M) (_ : Countable M)
    (hM : M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory),
    (letI := hM; letI := prunedUEVP_models_zf M; ¬ InternalChoice M) →
    ∀ N : ℕ, 1 ≤ N →
      ∃ (W : Type) (_ : SetStructure W) (_ : Nonempty W) (hZF : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
        (W↓[ℒₛₑₜ] ⊧* 𝗔𝗖) ∧
          letI := hZF; ∀ α : W, IsOrdinal α → ∃ κ : W, α ∈ κ ∧ IsCnExtendible N κ

/-- Every finite subset of `ZFC+VP` has a model, given consistency of `ZF+VP` and the finite
restoration input. This is the mathematical content of the paper's proof of Theorem B.

Take the countable pruned model `M` of `ZF+VP+UE+"no rank-Berkeley cardinals"`. If Choice
holds in `M`, then `M` itself models the finite subset. Otherwise feed `M` and the level
`effectiveLanguageReductionLevel u` of the Vopenka instances occurring in `u` to the finite
restoration input; the resulting `W` models `ZFC` and has unboundedly many
`C(N)`-extendible cardinals, which by `cnExtendible_unbounded_implies_effective_finite_vopenka` gives
every Vopenka sentence in `u`. -/
theorem finite_subset_zfcVP_models (hFR : FiniteRestorationInput) (h : Consistent zfVPTheory)
    (u : Finset SetTheorySentence) (hu : ↑u ⊆ zfcVPTheory) :
    ∃ (W : Type) (_ : Nonempty W) (_ : Structure ℒₛₑₜ W), W↓[ℒₛₑₜ] ⊧* (u : Theory ℒₛₑₜ) := by
  obtain ⟨M, hstr, hne, hcnt, hM⟩ := exists_countable_prunedUEVP_model h
  let iMs := hstr
  let iMn := hne
  let iMc := hcnt
  let iMu := hM
  let iMzf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := prunedUEVP_models_zf M
  by_cases hAC : InternalChoice M
  · let iMac : M↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := models_ac_of_internalChoice hAC
    refine ⟨M, hne, inferInstance, ⟨fun σ hσ ↦ ?_⟩⟩
    rcases hu hσ with (hφ | hφ) | ⟨ψ, rfl⟩
    · exact Theory.models M 𝗭𝗙 hφ
    · exact Theory.models M 𝗔𝗖 hφ
    · exact (eval_vopenkaSentence ψ).mpr (prunedUEVP_vopenkaInstance M ψ)
  · obtain ⟨W, hWstr, hWne, hWZF, hWAC, hWE⟩ :=
      hFR M hstr hne hcnt hM hAC (effectiveLanguageReductionLevel u)
        (one_le_effectiveLanguageReductionLevel u)
    let iWs := hWstr
    let iWn := hWne
    let iWzf := hWZF
    let iWac := hWAC
    refine ⟨W, hWne, inferInstance, ⟨fun σ hσ ↦ ?_⟩⟩
    have hσu : σ ∈ u := Finset.mem_coe.mp hσ
    rcases hu hσ with (hφ | hφ) | hφ
    · exact Theory.models W 𝗭𝗙 hφ
    · exact Theory.models W 𝗔𝗖 hφ
    · exact cnExtendible_unbounded_implies_effective_finite_vopenka u hWE hσu hφ

/-- The compactness half of Theorem B: consistency of `ZF+VP` gives consistency of
`ZFC+VP`, granted the finite restoration input. -/
theorem consistent_zfcVP_of_consistent_zfVP (hFR : FiniteRestorationInput)
    (h : Consistent zfVPTheory) : Consistent zfcVPTheory :=
  consistent_of_finite_subsets_models fun u hu ↦ finite_subset_zfcVP_models hFR h u hu

/-- The easy half of Theorem B, the paper's "by forgetting Choice": `ZF+VP` is a subtheory
of `ZFC+VP`. -/
theorem consistent_zfVP_of_consistent_zfcVP (h : Consistent zfcVPTheory) :
    Consistent zfVPTheory :=
  h.of_le (Entailment.WeakerThan.ofSubset fun _ hφ ↦ hφ.elim (fun h ↦ Or.inl (Or.inl h)) Or.inr)

/-- Theorem B: `Con(ZFC+VP)` if and only if `Con(ZF+VP)`. -/
theorem consistent_zfcVP_iff_consistent_zfVP (hFR : FiniteRestorationInput) :
    Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  ⟨consistent_zfVP_of_consistent_zfcVP, consistent_zfcVP_of_consistent_zfVP hFR⟩

end ZFVP
