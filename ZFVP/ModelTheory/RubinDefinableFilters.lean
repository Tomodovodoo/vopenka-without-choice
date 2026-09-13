import ZFVP.ModelTheory.MaximallyCompatibleFilters

/-! Enayat's Definition 5.13 taken literally is contradictory, and the repair.

Both readings of Definition 5.13 are stated in this file, on top of the Definition 5.10 vocabulary
of `ZFVP.ModelTheory.RubinModel`.

`ZFVP.IsRubin` transcribes Definition 5.13 of "Models of set theory: extensions and dead ends"
word for word: clause (b) asks that every maximal filter of a definable poset with a cofinal
`ω₁`-chain be coded in the model, that is, be the extension of a set. `not_isRubin` shows that no
model of ZF satisfies this, because the ordinals form a definable directed poset under inclusion
with no maximum element, they are a maximal filter over themselves, and a code for them would be a
set of all ordinals.

What Enayat's Appendix proof actually gives is that such a filter is parametrically definable.
`IsRubinDefinable` is Definition 5.13 with clause (b) weakened to that. Codedness comes back for
the poset used in Definition 5.16, `Fin(a,2)`, because there the filter is a subclass of a set and
separation turns definability into a code: this is
`IsRubinDefinable.isCoded_maximalFilter`. So the route from Definition 5.13 to Definition 5.16
survives the correction, and `IsRubinDefinable.isWeaklyRubin` runs it. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The ordinals as a definable poset -/

/-- Any two ordinals are contained in one of the two, since inclusion is total on ordinals. -/
theorem ordinal_directed {x y : V} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    ∃ z, IsOrdinal z ∧ x ⊆ z ∧ y ⊆ z := by
  have := hx
  have := hy
  rcases IsOrdinal.subset_or_supset (α := x) (β := y) with h | h
  · exact ⟨y, hy, h, subset_refl y⟩
  · exact ⟨x, hx, subset_refl x, h⟩

/-- The ordinals under inclusion are directed and have no maximum element: `∅` is an ordinal,
inclusion is total on ordinals, and `succ α` is an ordinal not contained in `α`. -/
theorem isDirectedNoMaxOn_isOrdinal :
    IsDirectedNoMaxOn (fun x : V ↦ IsOrdinal x) (· ⊆ ·) := by
  refine ⟨⟨∅, inferInstance⟩, fun x y hx hy ↦ ordinal_directed hx hy, ?_⟩
  rintro ⟨m, hm, hmax⟩
  have := hm
  exact mem_irrefl m (hmax (succ m) inferInstance m (mem_succ_self m))

/-- A set whose members are exactly the ordinals would be an ordinal, hence a member of itself. -/
theorem not_isCoded_isOrdinal : ¬ IsCoded (fun x : V ↦ IsOrdinal x) := by
  rintro ⟨m, hm⟩
  have hmord : IsOrdinal m :=
    IsOrdinal.of_transitive_of_isOrdinal
      ⟨fun y hy z hz ↦ by
        have : IsOrdinal y := (hm y).mp hy
        exact (hm z).mpr (IsOrdinal.of_mem hz)⟩
      fun β hβ ↦ (hm β).mp hβ
  exact mem_irrefl m ((hm m).mpr hmord)

/-- Enayat's Definition 5.13. Clause (a): every definable directed poset with no maximum element
has a cofinal chain of length `ω₁`. Clause (b): every maximal filter of a definable poset that has
a cofinal chain of length `ω₁` is coded in the model. Both clauses ask `le` to be a partial order
on `P`, which is what "poset" means.

This is kept only as the statement that `not_isRubin` below refutes; the definition the
development uses is `IsRubinDefinable`, further down this file. -/
def IsRubin (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  (∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) → (ℒₛₑₜ-relation[V] le) →
      IsPartialOrderOn P le → IsDirectedNoMaxOn P le → HasCofinalOmegaOneChainOn le P) ∧
    (∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) → (ℒₛₑₜ-relation[V] le) →
      IsPartialOrderOn P le → ∀ F : V → Prop, IsMaximalFilterOn P le F →
        HasCofinalOmegaOneChainOn le F → IsCoded F)

/-- Definition 5.13 read literally has no models. The ordinals under inclusion are a definable
poset which is directed and has no maximum element, so clause (a) gives them a cofinal
`ω₁`-chain; they are a maximal filter over themselves, so clause (b) codes them by a set; that
set is an ordinal and so a member of itself. -/
theorem not_isRubin (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ¬ IsRubin V := by
  rintro ⟨ha, hb⟩
  have hdef : ℒₛₑₜ-predicate[V] (fun x : V ↦ IsOrdinal x) := by definability
  have hpo : IsPartialOrderOn (fun x : V ↦ IsOrdinal x) (· ⊆ ·) := isPartialOrderOn_subset _
  have hchain : HasCofinalOmegaOneChainOn (· ⊆ ·) (fun x : V ↦ IsOrdinal x) :=
    ha _ _ hdef subset_definable hpo isDirectedNoMaxOn_isOrdinal
  have hmax : IsMaximalFilterOn (fun x : V ↦ IsOrdinal x) (· ⊆ ·) (fun x : V ↦ IsOrdinal x) :=
    ⟨⟨fun _ hx ↦ hx, fun x y hx hy ↦ ordinal_directed hx hy⟩,
      fun _ hF' _ x hx ↦ hF'.1 x hx⟩
  exact not_isCoded_isOrdinal (hb _ _ hdef subset_definable hpo _ hmax hchain)

/-! ### Definition 5.13 with the correction -/

/-- Enayat's Definition 5.13 with clause (b) repaired in two ways. Clause (a) is unchanged: every
definable directed poset with no maximum element has a cofinal chain of length `ω₁`. Clause (b)
asks that every maximal filter of a definable poset with a cofinal `ω₁`-chain be parametrically
definable, rather than coded by a set. The literal reading with `IsCoded` is refuted by
`not_isRubin`, and definability is what Enayat's own Appendix argument produces.

The second change is which reading of "maximal filter" clause (b) quantifies over. Definition
5.10(c) read as inclusion maximality is `IsMaximalFilterOn`; footnote 30 reads it as maximal
compatibility, which is `IsMaximallyCompatibleOn`, and that is the reading the Appendix argument
uses when it takes, for `q` outside the filter, a member of the filter with no common upper bound
with `q`. The two readings differ on a general poset: a chain `p₀ < p₁ < ...` together with a `q`
that has a common upper bound with each `pₙ` but with no cofinal set of them is inclusion maximal
while `q` is compatible with all of it. Clause (b) therefore quantifies over maximally compatible
filters. That asks for less than the inclusion reading would, and it is what the Appendix argument
delivers. On the poset of Definition 5.16, the internal finite partial functions from `a` into `2`,
the two readings agree, so the application in `isCoded_maximalFilter` loses nothing: see
`isMaximallyCompatibleOn_of_isMaximalInternalFilter`. -/
def IsRubinDefinable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  (∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) → (ℒₛₑₜ-relation[V] le) →
      IsPartialOrderOn P le → IsDirectedNoMaxOn P le → HasCofinalOmegaOneChainOn le P) ∧
    (∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) → (ℒₛₑₜ-relation[V] le) →
      IsPartialOrderOn P le → ∀ F : V → Prop, IsMaximallyCompatibleOn P le F →
        HasCofinalOmegaOneChainOn le F → ℒₛₑₜ-predicate[V] F)

/-- First clause of Definition 5.16: `([a]^{<ω})` has a cofinal chain of length `ω₁` for every
internally infinite `a`. Clause (a) is untouched by the correction, so the proof is the one that
clause (a) of `IsRubin` would give. -/
theorem IsRubinDefinable.hasCofinalOmegaOneChain_finiteSubsets (h : IsRubinDefinable V) (a : V)
    (ha : IsInternallyInfinite a) :
    HasCofinalOmegaOneChain (fun x ↦ x ∈ finiteSubsets a) :=
  (hasCofinalOmegaOneChainOn_subset_iff _).mp
    (h.1 (fun x ↦ x ∈ finiteSubsets a) (· ⊆ ·) (mem_finiteSubsets_definable a) subset_definable
      (isPartialOrderOn_subset _) (isDirectedNoMaxOn_finiteSubsets ha))

/-- Second clause of Definition 5.16, recovered from the weakened clause (b). The filter is
definable by the corrected clause, and all of its members lie in the set `Fin(a,2)`, so separation
turns the definition into a code. -/
theorem IsRubinDefinable.isCoded_maximalFilter (h : IsRubinDefinable V) (a : V) (F : V → Prop)
    (hF : IsMaximalInternalFilter (finitePartialFunctions a ((2 : ℕ) : V)) F)
    (hchain : HasCofinalOmegaOneChain F) : ∃ m : V, ∀ x : V, x ∈ m ↔ F x := by
  have hFdef : ℒₛₑₜ-predicate[V] F :=
    h.2 (fun x ↦ x ∈ finitePartialFunctions a ((2 : ℕ) : V)) (· ⊆ ·)
      (mem_finitePartialFunctions_definable a) subset_definable (isPartialOrderOn_subset _) F
      (isMaximallyCompatibleOn_of_isMaximalInternalFilter a F hF)
      ((hasCofinalOmegaOneChainOn_subset_iff F).mpr hchain)
  refine ⟨sep (finitePartialFunctions a ((2 : ℕ) : V)) F hFdef, fun x ↦ ?_⟩
  rw [mem_sep_iff]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hF.1.1 x hx, hx⟩⟩

/-- A rather classless model satisfying the corrected Definition 5.13 is weakly Rubin. Rather
classlessness is a hypothesis: Enayat derives it in Remark 5.14 from the ranked tree of classes,
which is not formalized here. -/
theorem IsRubinDefinable.isWeaklyRubin (h : IsRubinDefinable V) (hrc : IsRatherClassless V) :
    IsWeaklyRubin V :=
  ⟨hrc, fun a ha ↦ ⟨h.hasCofinalOmegaOneChain_finiteSubsets a ha,
    fun F hF hchain ↦ h.isCoded_maximalFilter a F hF hchain⟩⟩

end ZFVP
