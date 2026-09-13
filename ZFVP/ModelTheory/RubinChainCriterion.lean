import ZFVP.ModelTheory.RatherClasslessOfRubin
import ZFVP.ModelTheory.RubinChainStages
import ZFVP.ModelTheory.RubinDefinableFilters
import ZFVP.ModelTheory.RubinStage
import ZFVP.ModelTheory.OmegaOneChainColimit
import ZFVP.SetTheory.Rank

/-! # From an ω₁-chain of stages to a Rubin model

This is the verification half of Stage 1 of the Appendix of Enayat's "Models of set theory:
extensions and dead ends" (pages 24-25, "We now verify that `M` is a Rubin model"). The
ω₁-length construction is not carried out here; `RubinChain` packages the properties of the chain
that the construction delivers, and everything below is derived from them.

A `RubinChain W` is an increasing ω₁-indexed family of countable subsets of `W` that covers `W`,
each an elementary submodel, together with two closure properties:

* `upper` is Enayat's clause (2). A directed poset with no last element that is definable with
  parameters from stage `α` gets, at every later index `γ`, an element of the poset strictly above
  everything stage `γ` contributes to it, and that element enters every stage past `γ`.
* `reflect` combines his clauses (4) and (5). For a maximally compatible filter `F` of a definable
  poset that has a cofinal ω₁-chain and is not parametrically definable, some stage `α` reflects
  it: inside
  stage `α` every element of the poset outside `F` is incompatible with some element of `F`, and
  the trace of `F` on stage `α` cannot be separated from its complement in stage `α` by a set
  definable in `W`.

The two clauses of the corrected Definition 5.13 follow (`hasCofinalOmegaOneChainOn` and
`definable_of_maximalFilter`), hence `IsRubinDefinable` and `IsWeaklyRubin`, and the union has
cardinality `ℵ₁`. Rather classlessness is the two clauses fed to `ratherClassless_of_rubin_clauses`
from `ZFVP.ModelTheory.RatherClasslessOfRubin`, which runs Keisler's tree of classes.

One deviation from the printed proof. Enayat separates the trace of `F` from its complement in the
stage by the formula `x <_P e`, for `e` a link of the ω₁-chain above the whole trace. That formula
does not exclude the elements of the stage that are outside the poset `P`, and inseparability is
asked of the whole stage, so the separating set used here is `P x ∧ le x e`. The extra conjunct is
what makes the second half of the argument go through: an element of the stage outside `F` is
either outside `P`, and then it fails the first conjunct, or inside `P`, and then it is
incompatible with a filter element below `e`, so it cannot be below `e` either.

A second deviation, about which reading of Definition 5.10(c) the `reflect` field quantifies over.
Read as inclusion maximality, "maximal filter" is `IsMaximalFilterOn`; read as maximal
compatibility, the reading of footnote 30, it is `IsMaximallyCompatibleOn`. The two come apart on a
general poset, and it is the second that Enayat's verification uses, since it takes for each `q`
outside the filter a filter element with no common upper bound with `q`. The field is stated with
`IsMaximallyCompatibleOn`. That is the stronger condition on `F`, so the field ranges over fewer
filters and asks for less than the inclusion reading would. On the poset of Definition 5.16, the
internal finite partial functions from a set into `2`, the two readings agree, so nothing
downstream loses
coverage: see `isMaximallyCompatibleOn_of_isMaximalInternalFilter`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- The data Enayat's ω₁-length construction produces: an increasing chain of countable elementary
submodels covering `W`, closed under upper bounds for definable directed posets (`upper`) and
reflecting undefinable maximally compatible filters (`reflect`). -/
structure RubinChain (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] where
  /-- The stage of index `α`. -/
  stage : OmegaOne → Set W
  /-- The stages increase. -/
  mono : Monotone stage
  /-- The stages cover the model. -/
  cover : ∀ x : W, ∃ α, x ∈ stage α
  /-- Each stage is countable. -/
  countable : ∀ α, (stage α).Countable
  /-- Each stage is an elementary submodel. -/
  emb : ∀ α, ElementaryMap ↥(stage α) W
  /-- The embedding of a stage is the inclusion. -/
  emb_apply : ∀ (α) (x : ↥(stage α)), emb α x = (x : W)
  /-- Enayat's clause (2): a directed poset with no last element, definable with parameters from
  stage `α`, has at every later index `γ` an element strictly above everything stage `γ`
  contributes to it, and that element lies in every stage past `γ`. -/
  upper : ∀ (α γ : OmegaOne), α ≤ γ → ∀ (P : W → Prop) (le : W → W → Prop),
    DefinableOver (stage α) P → DefinableOverRel (stage α) le →
    IsPartialOrderOn P le → IsDirectedNoMaxOn P le →
    ∃ d, P d ∧ (∀ x, x ∈ stage γ → P x → le x d ∧ x ≠ d) ∧ ∀ γ', γ < γ' → d ∈ stage γ'
  /-- Enayat's clauses (4) and (5): an undefinable maximally compatible filter with a cofinal
  ω₁-chain is reflected by some stage. Inside that stage every element of the poset outside the
  filter is incompatible with some element of the filter, and the trace of the filter is
  inseparable from its complement in the stage. -/
  reflect : ∀ (P : W → Prop) (le : W → W → Prop), (ℒₛₑₜ-predicate[W] P) →
    (ℒₛₑₜ-relation[W] le) → IsPartialOrderOn P le → ∀ F : W → Prop,
    IsMaximallyCompatibleOn P le F → HasCofinalOmegaOneChainOn le F → ¬ (ℒₛₑₜ-predicate[W] F) →
    ∃ α : OmegaOne,
      (∀ q, q ∈ stage α → P q → ¬ F q →
         ∃ p, p ∈ stage α ∧ F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z) ∧
      Inseparable W (fun x ↦ x ∈ stage α ∧ F x) (fun x ↦ x ∈ stage α ∧ ¬ F x)

variable {W : Type u} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Clause (a) of Definition 5.13 -/

/-- Every definable directed poset with no maximum element has a cofinal chain of length `ω₁`.
Both the carrier and the order have all their parameters in a single stage `α₀`; reindex `ω₁`
strictly above `α₀` by `σ` and read off the upper bound `p i` that clause (2) gives at `σ i`. The
chain is strictly increasing because `p i` has entered stage `σ i'` by the time `p i'` is chosen,
and it is cofinal because a strictly monotone self-map of `ω₁` is inflationary. -/
theorem RubinChain.hasCofinalOmegaOneChainOn (C : RubinChain W) (P : W → Prop)
    (le : W → W → Prop) (hP : ℒₛₑₜ-predicate[W] P) (hle : ℒₛₑₜ-relation[W] le)
    (hpo : IsPartialOrderOn P le) (hdir : IsDirectedNoMaxOn P le) :
    HasCofinalOmegaOneChainOn le P := by
  obtain ⟨α₁, hα₁⟩ := exists_definableOver_of_definable C.stage C.mono C.cover hP
  obtain ⟨α₂, hα₂⟩ := exists_definableOverRel_of_definable C.stage C.mono C.cover hle
  have hPα : DefinableOver (C.stage (max α₁ α₂)) P := hα₁.mono (C.mono (le_max_left α₁ α₂))
  have hleα : DefinableOverRel (C.stage (max α₁ α₂)) le := hα₂.mono (C.mono (le_max_right α₁ α₂))
  obtain ⟨σ, hσmono, hσge⟩ := exists_strictMono_ge (max α₁ α₂)
  choose p hp1 hp2 hp3 using fun i ↦
    C.upper (max α₁ α₂) (σ i) (hσge i) P le hPα hleα hpo hdir
  refine ⟨p, hp1, ?_, ?_⟩
  · intro i i' hii'
    exact hp2 i' (p i) (hp3 i (σ i') (hσmono hii')) (hp1 i)
  · intro x hx
    obtain ⟨β, hβ⟩ := C.cover x
    exact ⟨β, (hp2 β x (C.mono hσmono.le_apply hβ) hx).1⟩

/-! ### Clause (b) of the corrected Definition 5.13 -/

/-- Every maximally compatible filter of a definable poset that has a cofinal chain of length
`ω₁` is
parametrically definable. Suppose not, and let `α` be a reflecting stage. The trace of `F` on
stage `α` is countable, so countably many links of the ω₁-chain of `F` bound it, and `ω₁` is
regular, so a single link `e` is above the whole trace. Then `P x ∧ le x e` is definable, it
contains the trace, and it misses the complement of the trace in the stage: an element of the
stage outside `F` is either outside `P`, or is incompatible with a filter element `p` of the
stage, which rules out `le x e` because `e` would then be a common upper bound of `p` and `x`.
That contradicts the inseparability clause. -/
theorem RubinChain.definable_of_maximalFilter (C : RubinChain W) (P : W → Prop)
    (le : W → W → Prop) (hP : ℒₛₑₜ-predicate[W] P) (hle : ℒₛₑₜ-relation[W] le)
    (hpo : IsPartialOrderOn P le) (F : W → Prop) (hF : IsMaximallyCompatibleOn P le F)
    (hchain : HasCofinalOmegaOneChainOn le F) : ℒₛₑₜ-predicate[W] F := by
  by_contra hFdef
  obtain ⟨α, hrefl, hinsep⟩ := C.reflect P le hP hle hpo F hF hchain hFdef
  obtain ⟨q, hq1, hq2, hq3⟩ := hchain
  have hcount : Set.Countable {x : W | x ∈ C.stage α ∧ F x} :=
    (C.countable α).mono fun x hx ↦ hx.1
  have : Countable ↥{x : W | x ∈ C.stage α ∧ F x} := hcount.to_subtype
  choose g hg using fun a : ↥{x : W | x ∈ C.stage α ∧ F x} ↦ hq3 a.1 a.2.2
  obtain ⟨k, hk⟩ := exists_upper_bound_of_countable g
  have hPq : ∀ i, P (q i) := fun i ↦ hF.1.1 (q i) (hq1 i)
  have hbound : ∀ x, x ∈ C.stage α → F x → le x (q k) := by
    intro x hxs hxF
    have hax := hg ⟨x, hxs, hxF⟩
    rcases eq_or_lt_of_le (hk ⟨x, hxs, hxF⟩) with h | h
    · rw [← h]; exact hax
    · exact hpo.2.1 x (q (g ⟨x, hxs, hxF⟩)) (q k) (hF.1.1 x hxF) (hPq _) (hPq k) hax
        (hq2 _ _ h).1
  have hX : ℒₛₑₜ-predicate[W] fun x ↦ P x ∧ le x (q k) := by
    have := hP
    have := hle
    definability
  refine hinsep ⟨fun x ↦ P x ∧ le x (q k), hX, ?_, ?_⟩
  · rintro x ⟨hxs, hxF⟩
    exact ⟨hF.1.1 x hxF, hbound x hxs hxF⟩
  · rintro x ⟨hxs, hxF⟩ ⟨hxP, hxle⟩
    obtain ⟨p, hps, hpF, hnz⟩ := hrefl x hxs hxP hxF
    exact hnz ⟨q k, hPq k, hbound p hps hpF, hxle⟩

/-! ### The three model-theoretic conclusions -/

/-- The union of the chain satisfies the corrected Definition 5.13. -/
theorem RubinChain.isRubinDefinable (C : RubinChain W) : IsRubinDefinable W :=
  ⟨fun P le hP hle hpo hdir ↦ C.hasCofinalOmegaOneChainOn P le hP hle hpo hdir,
    fun P le hP hle hpo F hF hchain ↦ C.definable_of_maximalFilter P le hP hle hpo F hF hchain⟩

/-- The union of the chain is rather classless, by Enayat's Remark 5.14 applied to the two
clauses. -/
theorem RubinChain.isRatherClassless (C : RubinChain W) : IsRatherClassless W :=
  ratherClassless_of_rubin_clauses
    (fun P le hP hle hpo hdir ↦ C.hasCofinalOmegaOneChainOn P le hP hle hpo hdir)
    (fun P le hP hle hpo F hF hchain ↦ C.definable_of_maximalFilter P le hP hle hpo F hF hchain)

/-- The union of the chain is weakly Rubin in the sense of Definition 5.16. -/
theorem RubinChain.isWeaklyRubin (C : RubinChain W) : IsWeaklyRubin W :=
  C.isRubinDefinable.isWeaklyRubin C.isRatherClassless

/-! ### Cardinality -/

/-- The union of the chain has exactly `ℵ₁` elements. At most, because it is the union of `ℵ₁`
countable stages; at least, because the cofinal `ω₁`-chain in the ordinals given by clause (a) is
injective. -/
theorem RubinChain.mk_eq_alephOne (C : RubinChain W) : Cardinal.mk W = Cardinal.aleph 1 := by
  refine le_antisymm ?_ ?_
  · have hsurj : Function.Surjective fun p : Σ a : OmegaOne, ↥(C.stage a) ↦ (p.2 : W) := by
      intro x
      obtain ⟨a, ha⟩ := C.cover x
      exact ⟨⟨a, ⟨x, ha⟩⟩, rfl⟩
    have h1 : Cardinal.mk W ≤ Cardinal.mk (Σ a : OmegaOne, ↥(C.stage a)) :=
      Cardinal.mk_le_of_surjective hsurj
    have h2 : Cardinal.sum (fun a : OmegaOne ↦ Cardinal.mk ↥(C.stage a))
        ≤ Cardinal.sum fun _ : OmegaOne ↦ Cardinal.aleph0.{u} := by
      refine Cardinal.sum_le_sum _ _ fun a ↦ ?_
      have := (C.countable a).to_subtype
      exact Cardinal.mk_le_aleph0
    rw [Cardinal.mk_sigma] at h1
    rw [Cardinal.sum_const, mk_omegaOne, Cardinal.lift_aleph, Ordinal.lift_one,
      Cardinal.lift_id'] at h2
    rw [Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
      Cardinal.aleph0_ne_zero] at h2
    exact h1.trans h2
  · obtain ⟨p, -, hp2, -⟩ :=
      C.hasCofinalOmegaOneChainOn (fun x : W ↦ IsOrdinal x) (· ⊆ ·) inferInstance subset_definable
        (isPartialOrderOn_subset _) isDirectedNoMaxOn_isOrdinal
    have hinj : Function.Injective p := by
      intro i i' h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (hp2 i i' hlt).2 h
      · exact (hp2 i' i hlt).2 h.symm
    have hlow : Cardinal.lift.{u} (Cardinal.mk OmegaOne) ≤ Cardinal.lift.{0} (Cardinal.mk W) :=
      Cardinal.lift_mk_le'.mpr ⟨⟨p, hinj⟩⟩
    rwa [mk_omegaOne, Cardinal.lift_aleph, Ordinal.lift_one, Cardinal.lift_id'] at hlow

end ZFVP
