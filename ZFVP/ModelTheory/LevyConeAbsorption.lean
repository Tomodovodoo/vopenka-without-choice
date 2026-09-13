import ZFVP.ModelTheory.CompleteEmbeddingCompletion
import ZFVP.ModelTheory.LevyConeAlgebraProperties
import ZFVP.SetTheory.FunctionComposition

/-! Absorption of a small poset into a cone of the Levy algebra.

Write `B` for `booleanConditions (levyCollapse κ) (levyOrder κ)` with the order
`booleanOrder (levyCollapse κ) (levyOrder κ)`, and `B↾a` for
`forcingCone B (booleanOrder …) a` with `restrictedOrder (booleanOrder …) (forcingCone …)`, the
spelling used in `LevyConeAlgebraProperties.lean` and `LevyConeCollapsing.lean`.

`CompleteEmbeddingCompletion.lean` proves that a forcing preorder `Q` with a top and of size at
most an infinite `lam ∈ κ` embeds completely into `B`
(`levy_exists_completeEmbedding_of_small`). This file moves that embedding down into a cone.

* `isCompleteEmbedding_compose_isomorphism`: a complete embedding followed by a forcing
  isomorphism of the target is again a complete embedding. The order and incompatibility clauses
  transport because an isomorphism reflects and preserves the order both ways; the maximal
  antichain clause transports because an isomorphism is onto its target, so a condition of the
  new target is the image of one of the old target.

* `levy_exists_completeEmbedding_coneRegular`: `Q` embeds completely into `B↾coneRegular p` for
  every condition `p` of the collapse. This composes the previous item with the inverse of
  `levy_forcingCone_coneRegular_isomorphic`, which says `B↾coneRegular p ≅ B`.

* `levy_exists_completeEmbedding_below`: below every nonzero `a` of `B` there is a nonzero `b ⊆ a`
  with `Q` embedding completely into `B↾b`. The witness is `b = coneRegular p` for a condition `p`
  supplied by `exists_coneRegular_subset`.

The gap to `b = a`, that is, to a complete embedding of `Q` into `B↾a` for an arbitrary nonzero
`a`, is homogeneity of the Levy algebra: `B↾a ≅ B` for every nonzero `a`. The repository does not
prove that, and `LevyBooleanHomogeneity.lean` records why the density argument used here cannot
be pushed to it. Only cones of the form `coneRegular p` are known to be isomorphic to `B`, and a
general nonzero `a` merely contains such a cone.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Values of a complete embedding -/

section Values

variable {P R P' R' e p : V}

/-- A complete embedding sends conditions to conditions. Reflexivity of `R` at `p` gives
`⟨e ‘ p, e ‘ p⟩ₖ ∈ R'`, and `R'` lives on `P' ×ˢ P'`. -/
theorem IsCompleteEmbedding.value_mem (hR : IsForcingPreorder P R)
    (hR' : IsForcingPreorder P' R') (he : IsCompleteEmbedding P R P' R' e) (hp : p ∈ P) :
    e ‘ p ∈ P' :=
  (kpair_mem_iff.mp (hR'.1 _ (he.2.2.1 p hp p hp (hR.2.1 p hp)))).1

/-- A complete embedding is an internal function from `P` to `P'`. -/
theorem IsCompleteEmbedding.mem_function (hR : IsForcingPreorder P R)
    (hR' : IsForcingPreorder P' R') (he : IsCompleteEmbedding P R P' R' e) : e ∈ P' ^ P := by
  have hfun : IsFunction e := he.1
  have h1 : e ∈ range e ^ P := by
    have := IsFunction.mem_function (V := V) e
    rwa [he.2.1] at this
  refine mem_function_of_mem_function_of_subset h1 (fun y hy ↦ ?_)
  obtain ⟨x, hx⟩ := mem_range_iff.mp hy
  have hxP : x ∈ P := by
    have := mem_domain_of_kpair_mem hx
    rwa [he.2.1] at this
  rw [← value_eq_of_kpair_mem hx]
  exact he.value_mem hR hR' hxP

end Values

/-! ### Transport of a complete embedding along an isomorphism of the target -/

section Transport

variable {P R P' R' Q S e f : V}

/-- A complete embedding of `(P, R)` into `(P', R')` followed by a forcing isomorphism of
`(P', R')` with `(Q, S)` is a complete embedding of `(P, R)` into `(Q, S)`. -/
theorem isCompleteEmbedding_compose_isomorphism (hR : IsForcingPreorder P R)
    (hR' : IsForcingPreorder P' R') (he : IsCompleteEmbedding P R P' R' e)
    (hf : IsForcingIsomorphism P' R' Q S f) : IsCompleteEmbedding P R Q S (compose e f) := by
  have hef : e ∈ P' ^ P := he.mem_function hR hR'
  have hc : compose e f ∈ Q ^ P := compose_function hef hf.1
  have hval : ∀ p ∈ P, (compose e f) ‘ p = f ‘ (e ‘ p) :=
    fun p hp ↦ value_compose_of_mem_function hef hf.1 hp
  have hmem : ∀ p ∈ P, e ‘ p ∈ P' := fun p hp ↦ he.value_mem hR hR' hp
  refine ⟨IsFunction.of_mem hc, domain_eq_of_mem_function hc, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rw [hval p hp, hval q hq]
    exact (hf.2.2.2 _ (hmem p hp) _ (hmem q hq)).mp (he.2.2.1 p hp q hq hpq)
  · intro p hp q hq hinc
    rw [hval p hp, hval q hq]
    rintro ⟨c, hcQ, hcp, hcq⟩
    obtain ⟨d, hd, rfl⟩ := isForcingIsomorphism_surjective hf c hcQ
    refine he.2.2.2.1 p hp q hq hinc ⟨d, hd, ?_, ?_⟩
    · exact (hf.2.2.2 d hd _ (hmem p hp)).mpr hcp
    · exact (hf.2.2.2 d hd _ (hmem q hq)).mpr hcq
  · intro A hA q hq
    obtain ⟨d, hd, rfl⟩ := isForcingIsomorphism_surjective hf q hq
    obtain ⟨a, ha, r, hr, hrd, hra⟩ := he.2.2.2.2 A hA d hd
    have haP : a ∈ P := hA.2.1 a ha
    refine ⟨a, ha, f ‘ r, function_value_mem hf.1 hr, ?_, ?_⟩
    · exact (hf.2.2.2 r hr d hd).mp hrd
    · rw [hval a haP]
      exact (hf.2.2.2 r hr _ (hmem a haP)).mp hra

end Transport

/-! ### Absorption below a condition cone of the Levy algebra -/

section Levy

variable {κ Q S one lam p a : V} [IsOrdinal κ]

/-- A forcing preorder with a top and of size at most an infinite `lam ∈ κ` embeds completely
into the cone of the Boolean completion of `Coll(ω, <κ)` below the regular cone of any condition
`p` of the collapse. -/
theorem levy_exists_completeEmbedding_coneRegular (hAC : InternalChoice V)
    (hR : IsForcingPreorder Q S) (htop : IsForcingTop Q S one) (hlam : lam ∈ κ)
    (hωlam : (ω : V) ⊆ lam) (hQ : Q ≤# lam) (hp : p ∈ levyCollapse κ) :
    ∃ e, IsCompleteEmbedding Q S
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) p))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) p))) e := by
  obtain ⟨e, he⟩ := levy_exists_completeEmbedding_of_small hAC hR htop hlam hωlam hQ
  obtain ⟨F, hF⟩ := levy_forcingCone_coneRegular_isomorphic hp
  exact ⟨compose e (converseGraph F), isCompleteEmbedding_compose_isomorphism hR
    (booleanOrder_poset (levyCollapse κ) (levyOrder κ)).1 he (isForcingIsomorphism_inverse hF)⟩

/-- Below every nonzero condition `a` of the Boolean completion of `Coll(ω, <κ)` there is a
nonzero `b ⊆ a` such that a forcing preorder with a top and of size at most an infinite
`lam ∈ κ` embeds completely into the cone below `b`.

This is not stated with `b = a`. That form is homogeneity of the Levy algebra, `B↾a ≅ B` for
arbitrary nonzero `a`, which the repository does not prove; see the module docstring. -/
theorem levy_exists_completeEmbedding_below (hAC : InternalChoice V)
    (hR : IsForcingPreorder Q S) (htop : IsForcingTop Q S one) (hlam : lam ∈ κ)
    (hωlam : (ω : V) ⊆ lam) (hQ : Q ≤# lam)
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ b ∈ booleanConditions (levyCollapse κ) (levyOrder κ), b ⊆ a ∧
      ∃ e, IsCompleteEmbedding Q S
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) b)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) b)) e := by
  obtain ⟨q, hq, hqa⟩ := exists_coneRegular_subset (levyCollapse_poset κ).1 ha
  exact ⟨coneRegular (levyCollapse κ) (levyOrder κ) q,
    coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hq, hqa,
    levy_exists_completeEmbedding_coneRegular hAC hR htop hlam hωlam hQ hq⟩

end Levy

end ZFVP
