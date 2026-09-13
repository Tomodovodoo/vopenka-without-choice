import ZFVP.SetTheory.MagidorLemmaThreeOne

/-! # How far one step of a rank embedding reaches, and what Magidor's Lemma 3.1 still needs

`ZFVP.SetTheory.MagidorLemmaThreeOne` proves Magidor's Lemma 3.1 for a coded membership embedding
`f : V_{lam+omega} → V_{lam'+omega}` with critical point `κ ∈ lam` in two cases: `lam` closed
under `f`, and `lam ⊆ f ‘ κ`. This module settles the question of whether the two cases exhaust
the possibilities, and isolates what is left.

## The two cases do not exhaust the possibilities

The disjunction

    (∀ δ ∈ lam, f ‘ δ ∈ lam) ∨ lam ⊆ f ‘ κ

is not a theorem. Take an embedding `j : V_del → V_del` with critical point `κ`, where `del` is
the limit of the critical sequence `κ, κ₁, κ₂, ...` (Kunen's theorem forbids `del` any larger, and
this is the axiom I3). For `α ∈ del` the restriction `j ↾ V_α` is an elementary embedding
`V_α → V_{j ‘ α}`, so

    f := j ↾ V_{κ₂+omega} : V_{κ₂+omega} → V_{κ₃+omega}

is a coded membership embedding with critical point `κ`. Put `lam := κ₂` and `lam' := κ₃`: both
are limit ordinals above `omega`, and `κ ∈ lam`. Now `lam` is not closed under `f`, because
`κ₁ ∈ lam` while `f ‘ κ₁ = κ₂ = lam ∉ lam`; and `lam ⊆ f ‘ κ = κ₁` fails because `κ₁ ∈ κ₂ = lam`.
So neither disjunct holds. The same configuration satisfies the marker equation `f ‘ lam = lam'`,
so adding that equation as a hypothesis does not rescue the disjunction either.

What is true, and is proved below as `magidorIterationReach`, is the same disjunction with the
critical point replaced by an unspecified ordinal of `lam`:

    (∀ δ ∈ lam, f ‘ δ ∈ lam) ∨ ∃ ν ∈ lam, κ ∈ ν ∧ lam ⊆ f ‘ ν.

The second disjunct says that one step of `f` starting at `ν` already passes above all of `lam`.
Bagaria's Definition 3.2 of extendibility asks for `ν = κ`, which is the case the one step proof
`magidorSupercompactUpTo_of_subset_value` handles. The residual situation is `ν ∈ lam` with
`κ ∈ ν`, and the counterexample above shows that it cannot be argued away.

## What is missing

Bagaria's proof of Lemma 3.1 (in *C(n)-cardinals*, section 3) fixes `γ < lam`, and when
`j ‘ κ ≤ γ` writes `j_1 = j` and `j_{m+1} = j ∘ j_m`, then uses `j_m` with `j_m ‘ κ > γ` in place
of `j`. He does not say on what set the composite is defined. It is applied to subsets of
`P_κ(γ)`, and the `j`-image of such a subset has rank about `j ‘ γ`, which is above `lam` in
exactly the residual situation. So the published proof leaves the same step unjustified that this
formalization cannot supply, and the gap here is not an artefact of the small embedding form of
the conclusion.

The step is packaged as `HasReachingEmbedding κ γ`: some coded membership embedding of rank
stages `V_{rho+omega} → V_{rho'+omega}` has critical point `κ`, has `γ` below `rho`, and moves `κ`
past `γ`. Bagaria's `j_m` is meant to be such an embedding. From it Magidor's predicate at `γ`
follows by one step (`magidorSupercompactAt_of_reaching`), so `ReachesEveryStage lam κ` yields
Lemma 3.1 for `lam` with no case hypothesis at all
(`magidorSupercompactUpTo_of_reaching`), and combining that with the closed case gives
`magidorSupercompactUpTo_of_criticalPoint_of_reaching`, which is Lemma 3.1 with the residual
situation as its only assumption.

The predicate is not vacuous: `reachesEveryStage_of_subset_value` proves it from `lam ⊆ f ‘ κ`,
using `f` itself, so the second of the two known cases factors through it.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An embedding of rank stages that reaches `γ`: its critical point is `κ`, its source height is
above `γ`, and it moves `κ` past `γ`. This is what Bagaria's iterate `j_m` is supposed to be. -/
def HasReachingEmbedding (κ γ : V) : Prop :=
  ∃ rho rho' k, IsLimitOrdinal rho ∧ (ω : V) ∈ rho ∧ IsLimitOrdinal rho' ∧ (ω : V) ∈ rho' ∧
    IsCodedMembershipEmbedding (hierarchy (ordinalAdd rho (ω : V)))
      (hierarchy (ordinalAdd rho' (ω : V))) k ∧
    IsCriticalPoint (hierarchy (ordinalAdd rho (ω : V))) k κ ∧ γ ∈ rho ∧ γ ∈ k ‘ κ

/-- A reaching embedding at every rank below `lam` that is above `κ`. -/
def ReachesEveryStage (lam κ : V) : Prop :=
  ∀ γ ∈ lam, κ ∈ γ → HasReachingEmbedding κ γ

/-- A reaching embedding at `γ` gives Magidor's small embedding at `γ`, by the one step argument
`magidorSupercompactAt_of_mem_value` applied to the reaching embedding. -/
theorem magidorSupercompactAt_of_reaching {κ γ : V}
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hκγ : κ ∈ γ) (hr : HasReachingEmbedding κ γ) : IsMagidorSupercompactAt κ γ := by
  obtain ⟨rho, rho', k, hlim, hω, hlim', hω', hk, hcrit, hγrho, hγv⟩ := hr
  let := hlim.1
  let := hlim'.1
  exact magidorSupercompactAt_of_mem_value hlim hω hlim' hω' hF hk hcrit hκγ hγrho hγv

/-- Magidor's Lemma 3.1 for `lam`, with the reaching embeddings as the only hypothesis. No case
distinction on `lam` is used. -/
theorem magidorSupercompactUpTo_of_reaching {lam κ : V}
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hr : ReachesEveryStage lam κ) : IsMagidorSupercompactUpTo κ lam :=
  fun γ hγ _ hκγ ↦ magidorSupercompactAt_of_reaching hF hκγ (hr γ hγ hκγ)

/-- A coded embedding of transitive sets is monotone on ordinals of its source. -/
theorem value_ordinal_subset {A B f a b : V} [IsTransitive A] [IsTransitive B]
    [IsOrdinal a] [IsOrdinal b] (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ⊆ b) : f ‘ a ⊆ f ‘ b := by
  rcases IsOrdinal.subset_iff.mp hab with he | hlt
  · exact he ▸ subset_refl _
  · let := h.value_ordinal (inferInstance : IsOrdinal b) hb
    exact IsOrdinal.toIsTransitive.transitive _ ((h.value_mem_iff ha hb).mpr hlt)

/-- Every ordinal of `lam` lies in the stage `V_{lam+omega}`. -/
theorem ordinal_mem_source {lam δ : V} [IsOrdinal lam] (hδ : δ ∈ lam) :
    δ ∈ hierarchy (ordinalAdd lam (ω : V)) := by
  let := IsOrdinal.of_mem hδ
  exact ordinal_mem_hierarchy_iff.mpr
    (IsOrdinal.toIsTransitive.mem_trans hδ (ordinalAdd_omega_gt lam))

section Reach

variable {lam lam' f κ : V} [IsOrdinal lam] [IsOrdinal lam']
  (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
  (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
  (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
  (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
    (hierarchy (ordinalAdd lam' (ω : V))) f)
  (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ)

include h

/-- The image of an ordinal of `lam` is an ordinal. -/
theorem value_ordinal_of_mem_lam {δ : V} (hδ : δ ∈ lam) : IsOrdinal (f ‘ δ) := by
  let := IsOrdinal.of_mem hδ
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  exact h.value_ordinal inferInstance (ordinal_mem_source hδ)

/-- An ordinal of `lam` whose image leaves `lam` has its image above all of `lam`. -/
theorem lam_subset_value_of_value_not_mem {δ : V} (hδ : δ ∈ lam) (hv : f ‘ δ ∉ lam) :
    lam ⊆ f ‘ δ := by
  let := value_ordinal_of_mem_lam h hδ
  rcases IsOrdinal.mem_trichotomy lam (f ‘ δ) with hm | he | hm
  · exact IsOrdinal.toIsTransitive.transitive _ hm
  · exact he ▸ subset_refl _
  · exact absurd hm hv

/-- `lam` fails to be closed under `f` exactly when one step of `f` from inside `lam` already
passes above all of `lam`. -/
theorem not_closed_iff_exists_reach :
    (¬ ∀ δ ∈ lam, f ‘ δ ∈ lam) ↔ ∃ ν ∈ lam, lam ⊆ f ‘ ν := by
  classical
  constructor
  · intro hnot
    by_contra hc
    refine hnot fun δ hδ ↦ ?_
    by_contra hv
    exact hc ⟨δ, hδ, lam_subset_value_of_value_not_mem h hδ hv⟩
  · rintro ⟨ν, hν, hsub⟩ hclosed
    exact mem_irrefl (f ‘ ν) (hsub _ (hclosed ν hν))

/-- The ordinals of `lam` whose image stays in `lam` form an initial segment of `lam`. -/
theorem value_mem_of_subset {δ ε : V} (hδ : δ ∈ lam) (hε : ε ∈ lam) (hsub : ε ⊆ δ)
    (hv : f ‘ δ ∈ lam) : f ‘ ε ∈ lam := by
  let := IsOrdinal.of_mem hδ
  let := IsOrdinal.of_mem hε
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hmono : f ‘ ε ⊆ f ‘ δ :=
    value_ordinal_subset h (ordinal_mem_source hε) (ordinal_mem_source hδ) hsub
  let := value_ordinal_of_mem_lam h hε
  let := value_ordinal_of_mem_lam h hδ
  rcases IsOrdinal.subset_iff.mp hmono with he | hlt
  · exact he ▸ hv
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hv

/-- The ordinals of `lam` whose image passes above all of `lam` form a final segment of `lam`. -/
theorem lam_subset_value_of_subset {ν ν' : V} (hν : ν ∈ lam) (hν' : ν' ∈ lam) (hsub : ν ⊆ ν')
    (hreach : lam ⊆ f ‘ ν) : lam ⊆ f ‘ ν' := by
  let := IsOrdinal.of_mem hν
  let := IsOrdinal.of_mem hν'
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hmono : f ‘ ν ⊆ f ‘ ν' :=
    value_ordinal_subset h (ordinal_mem_source hν) (ordinal_mem_source hν') hsub
  exact fun x hx ↦ hmono x (hreach x hx)

include hlim hκ

omit hlim in
/-- Outside the case `lam ⊆ f ‘ κ`, every ordinal from which one step of `f` passes above all of
`lam` is above the critical point. This is the sense in which the residual situation is a genuine
residue: the reaching ordinal cannot be pushed down to `κ`. -/
theorem criticalPoint_mem_of_reach (hnot : ¬ lam ⊆ f ‘ κ) {ν : V} (hν : ν ∈ lam)
    (hreach : lam ⊆ f ‘ ν) : κ ∈ ν := by
  let := hκ.ordinal
  let := IsOrdinal.of_mem hν
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  rcases IsOrdinal.mem_trichotomy κ ν with hm | he | hm
  · exact hm
  · exact absurd (he ▸ hreach) hnot
  · have hmono : f ‘ ν ⊆ f ‘ κ :=
      value_ordinal_subset h (ordinal_mem_source hν) hκ.mem_domain
        (IsOrdinal.toIsTransitive.transitive _ hm)
    exact absurd (fun x hx ↦ hmono x (hreach x hx)) hnot

/-- The reach dichotomy, and the honest form of the case hypothesis of
`magidorSupercompactUpTo_of_criticalPoint`: either `lam` is closed under `f`, or one step of `f`
from some ordinal of `lam` above `κ` already passes above all of `lam`. The version with `κ` in
place of `ν` is not a theorem; see the module docstring. -/
theorem magidorIterationReach (hκlam : κ ∈ lam) :
    (∀ δ ∈ lam, f ‘ δ ∈ lam) ∨ ∃ ν ∈ lam, κ ∈ ν ∧ lam ⊆ f ‘ ν := by
  classical
  by_cases hclosed : ∀ δ ∈ lam, f ‘ δ ∈ lam
  · exact Or.inl hclosed
  refine Or.inr ?_
  obtain ⟨δ, hδ, hreach⟩ := (not_closed_iff_exists_reach h).mp hclosed
  let := hκ.ordinal
  let := IsOrdinal.of_mem hδ
  have hsκ : succ κ ∈ lam := succ_mem_of_limitOrdinal hlim hκlam
  let := IsOrdinal.of_mem hsκ
  have hνord : IsOrdinal (δ ∪ succ κ) := ordinal_union_ordinal δ (succ κ)
  let := hνord
  have hνlam : δ ∪ succ κ ∈ lam := union_mem_of_ordinals hδ hsκ
  refine ⟨δ ∪ succ κ, hνlam, ?_, ?_⟩
  · exact mem_union_iff.mpr (Or.inr (mem_succ_self κ))
  · exact lam_subset_value_of_subset h hδ hνlam (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hreach

include hωlam hlim' hωlam' hF

omit [IsOrdinal lam] [IsOrdinal lam'] hF in
/-- If one step of `f` already passes above all of `lam`, then `f` itself is a reaching embedding
at every rank below `lam`. This is the case Bagaria's Definition 3.2 builds in, and it shows that
`ReachesEveryStage` is not a vacuous condition. -/
theorem reachesEveryStage_of_subset_value (hsub : lam ⊆ f ‘ κ) : ReachesEveryStage lam κ :=
  fun γ hγ _ ↦ ⟨lam, lam', f, hlim, hωlam, hlim', hωlam', h, hκ, hγ, hsub γ hγ⟩

/-- Magidor's predicate holds unconditionally at every rank that is both below `lam` and below
`f ‘ κ`: one step of `f` reaches those and no iterate is needed. -/
theorem magidorSupercompactUpTo_inter_value :
    IsMagidorSupercompactUpTo κ (lam ∩ f ‘ κ) := by
  intro γ hγ _ hκγ
  obtain ⟨hγlam, hγv⟩ := mem_inter_iff.mp hγ
  exact magidorSupercompactAt_of_mem_value hlim hωlam hlim' hωlam' hF h hκ hκγ hγlam hγv

/-- Magidor's Lemma 3.1 with no case hypothesis on `lam`, assuming only that the residual
situation carries reaching embeddings. Both halves of
`magidorSupercompactUpTo_of_criticalPoint` are absorbed: if `lam` is closed under `f` the closed
case proof applies, and otherwise the hypothesis supplies the embedding that Bagaria's `j_m` is
meant to be. What is not proved anywhere is that the residual situation does carry them; by the
counterexample in the module docstring, the residual situation itself cannot be excluded. -/
theorem magidorSupercompactUpTo_of_criticalPoint_of_reaching (hAC : InternalChoice V)
    (hreach : (¬ ∀ δ ∈ lam, f ‘ δ ∈ lam) → ReachesEveryStage lam κ) :
    IsMagidorSupercompactUpTo κ lam := by
  classical
  by_cases hclosed : ∀ δ ∈ lam, f ‘ δ ∈ lam
  · exact magidorSupercompactUpTo_of_closed hlim hωlam hlim' hωlam' hF h hκ hAC hclosed
  · exact magidorSupercompactUpTo_of_reaching hF (hreach hclosed)

end Reach

end ZFVP
