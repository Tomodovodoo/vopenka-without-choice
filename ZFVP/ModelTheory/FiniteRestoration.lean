import ZFVP.ModelTheory.ConsistencyTransferPassage
import ZFVP.ModelTheory.FiniteRestorationGround
import ZFVP.ModelTheory.EndpointRankModel
import ZFVP.ModelTheory.EndpointCheckRank
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.ModelTheory.WoodinEndpointPoset
import ZFVP.SetTheory.SmallEmbeddingLevels
import ZFVP.SetTheory.LimitStageEmbedding

/-! # Theorem thm:finite-restoration, assembled from named hypotheses

This is the last module of node W09.  It puts the ground-model half
(`ZFVP.ModelTheory.FiniteRestorationGround`) together with the endpoint model
(`ZFVP.ModelTheory.EndpointRankModel`) and the Bagaria-Poveda criterion
(`ZFVP.SetTheory.SmallEmbeddingLevels`), and discharges the hypothesis
`FiniteRestorationInput` of `ZFVP.ModelTheory.ConsistencyTransferPassage` from the facts that
nodes W02, W03, W04 and W08 still owe.

Those facts are collected in `FiniteRestorationInterfaces`.  Nothing here proves anything about
Woodin's iteration: the two interface fields say that the poset is definable enough for the
stage dictionary (W02) and that a suitable endpoint of a `Q_Λ`-generic extension carries the
data of `EndpointWitnessData` (W02 for the construction, W03 for the ZFC endpoint, W04 for the
embedding lift, W06 for the finite windows read at the endpoint).

What this module does prove is the paper's assembly: the endpoint rank `M = (V[G])_Λ` models
`ZFC`, and the small-embedding criterion holds at unboundedly many of its ordinals, so `M` has
a proper class of `C^(N)`-extendible cardinals.
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

-- The level definitions unfold into the recursions that compute Levy bounds from formula codes.
-- Only the inequalities exported by `ZFVP.SetTheory.FiniteRestorationLevel` are used below, so
-- they are sealed here; otherwise elaboration loops inside those recursions.
attribute [local irreducible] woodinWindowLevel finiteRestorationReflectionLevel
  finiteRestorationWitnessLevel finiteRestorationLevel

variable {M : Type} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- What W02, W03, W04 and W06 owe at one endpoint `Λ` of one ground model.

The fields are stated in the order the proof needs them: `rankHeight` first, because the ZF
structure of the endpoint rank `A.endpointRank Λ` is what later fields talk about, and
`checkRank` before the fields that use `A.endpointCheck`.  `checkRank` is not an extra
assumption: `EndpointWitnessData.checkRank_of` derives it from `topRank` and the level of `Λ`. -/
structure EndpointWitnessData (N : ℕ) (Q : List (SetTheorySemisentence 6)) (Λ : M)
    (A : ForcingContext M) : Prop where
  /-- W03, the ZFC endpoint: the endpoint height is a ZF rank of the extension. -/
  rankHeight : IsRankCriterionHeight (A.check Λ)
  /-- W02: the forcing is Woodin's endpoint forcing at `Λ`. -/
  poset : A.P = woodinEndpointPoset Λ
  /-- W02: with Woodin's order at `Λ`. -/
  order : A.R = woodinEndpointOrder Λ
  /-- W02: the top condition has rank below `Λ`, which is what `checkRank_of_cn` needs. -/
  topRank : A.one ∈ hierarchy Λ
  /-- W03: the check map does not raise rank past the endpoint.  Redundant, see
  `EndpointWitnessData.checkRank_of`. -/
  checkRank : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ)
  /-- W03, the ZFC endpoint: Choice holds there. -/
  choice :
    letI := A.endpointRank_nonempty rankHeight
    letI := A.endpointRank_models_zf rankHeight
    InternalChoice (A.endpointRank Λ)
  /-- W03: the forcing adds no ordinals below `Λ`. -/
  ordinals : ∀ β : A.Model, IsOrdinal β → β ∈ A.check Λ → ∃ b : M, b ∈ Λ ∧ β = A.check b
  /-- W03, as in the proof of lem:rank-Berkeley-descent: an `E_{s_N}`-cardinal of the ground
  model is still a cardinal at the endpoint. -/
  cardinal :
    letI := A.endpointRank_nonempty rankHeight
    letI := A.endpointRank_models_zf rankHeight
    ∀ δ : M, δ ∈ Λ → IsCnExtendible (finiteRestorationWitnessLevel N Q) δ →
      ∀ hδ : δ ∈ hierarchy Λ, IsInitialOrdinal (A.endpointCheck Λ checkRank δ hδ)
  /-- W06, finite windows read at the endpoint: a marked stage is a `C^(N+1)` stage of the
  endpoint. -/
  marked :
    letI := A.endpointRank_nonempty rankHeight
    letI := A.endpointRank_models_zf rankHeight
    ∀ θ : M, θ ∈ Λ → IsCnExtendible (finiteRestorationWitnessLevel N Q) θ →
      ∀ hθ : θ ∈ hierarchy Λ, Cn (N + 1) (A.endpointCheck Λ checkRank θ hθ)
  /-- W04, the rank embedding lift with graph bounds: the reflected tuple of the ground model
  gives a small embedding inside the endpoint, whose graph is an element of the endpoint. -/
  lift :
    letI := A.endpointRank_nonempty rankHeight
    letI := A.endpointRank_models_zf rankHeight
    ∀ η δ θ ρ α x : M, δ ∈ Λ → θ ∈ Λ → ρ ∈ Λ →
      IsCnExtendible (finiteRestorationWitnessLevel N Q) δ →
      IsCnExtendible (finiteRestorationWitnessLevel N Q) θ →
      δ ∈ θ → α ∈ θ → x ∈ hierarchy ρ →
      Reflects (finiteRestorationReflectionLevel N Q) (woodinStageDictionary N Q)
        ![η, δ, θ, ρ, α, x] →
      ∀ (hθ : θ ∈ hierarchy Λ) (hδ : δ ∈ hierarchy Λ) (hα : α ∈ hierarchy Λ),
        ∃ d t a e : A.endpointRank Λ,
          d ∈ t ∧ t ∈ A.endpointCheck Λ checkRank δ hδ ∧ a ∈ t ∧ Cn (N + 1) t ∧
          IsCodedMembershipEmbedding (hierarchy t)
            (hierarchy (A.endpointCheck Λ checkRank θ hθ)) e ∧
          IsCriticalPoint (hierarchy t) e d ∧
          e ‘ d = A.endpointCheck Λ checkRank δ hδ ∧
          e ‘ a = A.endpointCheck Λ checkRank α hα

/-- The `checkRank` field of `EndpointWitnessData` follows from `topRank` and the level of `Λ`,
by `ForcingContext.checkRank_of_cn`, so it adds no strength to the interface. -/
theorem EndpointWitnessData.checkRank_of {N : ℕ} {Q : List (SetTheorySemisentence 6)} {Λ : M}
    {A : ForcingContext M} (hΛ : IsCnExtendible (finiteRestorationLevel N Q) Λ)
    (htop : A.one ∈ hierarchy Λ) : ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ) :=
  A.checkRank_of_cn ((cn_of_finiteRestorationLevel hΛ).of_le (by omega)) htop

/-- The complete set of named hypotheses of node W09. -/
structure FiniteRestorationInterfaces (Q : List (SetTheorySemisentence 6)) : Prop where
  /-- W02 poset coding: in every ZF model, the code of `Q_θ` with its order and restriction maps
  lies in `V_ρ` and satisfies the clause list `Q`.  This is the third group of clauses of `Ξ_N`,
  for which the codebase has no named formula. -/
  posetCode : ∀ (K : Type) (iS : SetStructure K) (iN : Nonempty K),
      letI := iS
      letI := iN
      ∀ hZF : K↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      letI := hZF
      ∀ (N : ℕ) (θ ρ : K), IsCnExtendible (finiteRestorationWitnessLevel N Q) θ →
        Cn (finiteRestorationReflectionLevel N Q) ρ → ordinalAdd θ (ω : K) ∈ ρ →
        ∃ x : K, x ∈ hierarchy ρ ∧ ∀ a b c : K, ∀ e ∈ Q, e.Evalb ![a, b, θ, ρ, c, x]
  /-- W02 construction plus W03/W04 at a sufficiently large endpoint: in a countable ZF model
  where Choice fails there is an `E_{t_N}`-cardinal `Λ` above the least dependent-choice failure
  and a `Q_Λ`-generic extension carrying the endpoint data. -/
  endpoint : ∀ (K : Type) (iS : SetStructure K) (iN : Nonempty K) (_ : Countable K),
      letI := iS
      letI := iN
      ∀ hZF : K↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      letI := hZF
      ¬ InternalChoice K → ∀ N : ℕ, 1 ≤ N →
      ∃ (Λ : K) (A : ForcingContext K) (_ : IsCnExtendible (finiteRestorationLevel N Q) Λ),
        EndpointWitnessData N Q Λ A

/-- Theorem thm:finite-restoration: the endpoint rank `M = (V[G])_Λ` models `ZFC` and has a
proper class of `C^(N)`-extendible cardinals.

The proof is the last four paragraphs of the paper.  `ZF` comes from the rank criterion at the
endpoint height and `AC` from `EndpointWitnessData.choice`.  For the extendibles, an ordinal of
the endpoint is pulled back to the ground model by `ordinals`, `exists_reflected_stage` produces
an `E_{s_N}`-cardinal `δ` above it together with the reflection data at every higher
`E_{s_N}`-cardinal `θ`, `cardinal` makes the image of `δ` an initial ordinal of the endpoint,
`marked` makes the image of `θ` a `C^(N+1)` stage of the endpoint, and `lift` turns the
reflection data into the small embedding the Bagaria-Poveda criterion asks for. -/
theorem finite_restoration_of_interfaces {Q : List (SetTheorySemisentence 6)}
    (h : FiniteRestorationInterfaces Q) : FiniteRestorationInput := by
  intro K hstr hne hcnt hM hAC N hN
  let := hstr
  let := hne
  let := hcnt
  let := hM
  let hzf : K↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := prunedUEVP_models_zf K
  obtain ⟨Λ, A, hΛ, hd⟩ := h.endpoint K hstr hne hcnt hzf hAC N hN
  let iWn : Nonempty (A.endpointRank Λ) := A.endpointRank_nonempty hd.rankHeight
  let iWz : (A.endpointRank Λ)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := A.endpointRank_models_zf hd.rankHeight
  refine ⟨A.endpointRank Λ, inferInstance, iWn, iWz,
    A.endpointRank_models_ac hd.choice, ?_⟩
  -- the ground-model data
  have hΛo : IsOrdinal Λ := hΛ.1.1
  have hcΛo : IsOrdinal (A.check Λ) := inferInstance
  have hTr : IsTransitive (hierarchy (A.check Λ)) := hierarchy_transitive _
  obtain ⟨k, hk, -⟩ := exists_reflection_predecessor (N := N) (Q := Q)
  have hUE : ∀ α : K, IsOrdinal α →
      ∃ κ : K, α ∈ κ ∧ IsCnExtendible (finiteRestorationWitnessLevel N Q) κ := by
    have hs : K↓[ℒₛₑₜ] ⊧ unboundedExtendibilitySentence (k + 1) :=
      Theory.models K zfUEVPNoRankBerkeleyTheory (Or.inr (Or.inr ⟨k, rfl⟩))
    rw [← hk] at hs
    exact (eval_unboundedExtendibilitySentence _).mp hs
  have hQ := h.posetCode K hstr hne hzf N
  -- pulling an ordinal of the endpoint back to the ground model
  have pull : ∀ y : A.endpointRank Λ, IsOrdinal y →
      ∃ b : K, ∃ hbΛ : b ∈ Λ,
        y = A.endpointCheck Λ hd.checkRank b (ordinal_subset_hierarchy Λ b hbΛ) := by
    intro y hy
    have hyv : IsOrdinal y.val := (setDomain_isOrdinal_iff _ y).mp hy
    let := hyv
    have hymem : y.val ∈ A.check Λ := ordinal_mem_hierarchy_iff.mp y.property
    obtain ⟨b, hbΛ, hb⟩ := hd.ordinals y.val hyv hymem
    exact ⟨b, hbΛ, Subtype.ext hb⟩
  -- the Bagaria-Poveda criterion at level `N`
  refine cnExtendible_unbounded_of_smallEmbeddingCriterion' hN ?_
  intro y hy
  obtain ⟨b, hbΛ, rfl⟩ := pull y hy
  obtain ⟨δ, hδΛ, hbδ, hδE, hmain⟩ := exists_reflected_stage hΛ hUE hQ hbΛ
  have hδh : δ ∈ hierarchy Λ := ordinal_subset_hierarchy Λ δ hδΛ
  refine ⟨A.endpointCheck Λ hd.checkRank δ hδh,
    (A.endpointCheck_mem_iff Λ hd.checkRank _ hδh).mpr hbδ, hd.cardinal δ hδΛ hδE hδh, ?_⟩
  intro z hz
  obtain ⟨c, hcΛ, rfl⟩ := pull z hz
  have hch : c ∈ hierarchy Λ := ordinal_subset_hierarchy Λ c hcΛ
  have hco : IsOrdinal c := IsOrdinal.of_mem hcΛ
  have hδo : IsOrdinal δ := IsOrdinal.of_mem hδΛ
  -- an `E_{s_N}`-cardinal `θ` below `Λ` above both `c` and `δ`
  obtain ⟨θ, hθΛ, hδθ, hθE, hcθ⟩ : ∃ θ : K, θ ∈ Λ ∧ δ ∈ θ ∧
      IsCnExtendible (finiteRestorationWitnessLevel N Q) θ ∧ c ∈ θ := by
    rcases IsOrdinal.mem_trichotomy (α := c) (β := δ) with hlt | heq | hgt
    · obtain ⟨θ, hθΛ, hδθ, hθE⟩ := exists_witnessLevel_cnExtendible_below hΛ hUE hδΛ
      have : IsOrdinal θ := IsOrdinal.of_mem hθΛ
      exact ⟨θ, hθΛ, hδθ, hθE, IsOrdinal.toIsTransitive.mem_trans hlt hδθ⟩
    · subst heq
      obtain ⟨θ, hθΛ, hδθ, hθE⟩ := exists_witnessLevel_cnExtendible_below hΛ hUE hδΛ
      exact ⟨θ, hθΛ, hδθ, hθE, hδθ⟩
    · obtain ⟨θ, hθΛ, hcθ, hθE⟩ := exists_witnessLevel_cnExtendible_below hΛ hUE hcΛ
      have : IsOrdinal θ := IsOrdinal.of_mem hθΛ
      exact ⟨θ, hθΛ, IsOrdinal.toIsTransitive.mem_trans hgt hcθ, hθE, hcθ⟩
  have hθo : IsOrdinal θ := IsOrdinal.of_mem hθΛ
  have hθh : θ ∈ hierarchy Λ := ordinal_subset_hierarchy Λ θ hθΛ
  refine ⟨A.endpointCheck Λ hd.checkRank θ hθh,
    (A.endpointCheck_mem_iff Λ hd.checkRank _ hθh).mpr hcθ, hd.marked θ hθΛ hθE hθh, ?_⟩
  intro w hw
  have hecθ : IsOrdinal (A.endpointCheck Λ hd.checkRank θ hθh) :=
    (setDomain_isOrdinal_iff _ _).mpr ((A.check_ordinal_iff θ).mpr hθo)
  obtain ⟨a, haΛ, rfl⟩ := pull w (IsOrdinal.of_mem hw)
  have hah : a ∈ hierarchy Λ := ordinal_subset_hierarchy Λ a haΛ
  have haθ : a ∈ θ := (A.endpointCheck_mem_iff Λ hd.checkRank hah hθh).mp hw
  obtain ⟨ρ, x, hρΛ, hxρ, hrefl⟩ := hmain θ hθΛ hδθ hθE a haθ
  exact hd.lift b δ θ ρ a x hδΛ hθΛ hρΛ hδE hθE hδθ haθ hxρ hrefl hθh hδh hah

/-- Theorem B with the finite restoration hypothesis discharged into the interfaces of W09. -/
theorem consistent_zfcVP_iff_consistent_zfVP_of_interfaces
    {Q : List (SetTheorySemisentence 6)} (h : FiniteRestorationInterfaces Q) :
    Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  consistent_zfcVP_iff_consistent_zfVP (finite_restoration_of_interfaces h)

end ZFVP
