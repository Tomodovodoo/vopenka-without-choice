import ZFVP.SetTheory.WoodinSupercompactHighCritical
import ZFVP.SetTheory.WoodinSupercompactInaccessible

/-! # Woodin's small-embedding supercompactness and Magidor's characterization

`IsWoodinSupercompact κ` (ZFVP/SetTheory/WoodinSupercompact.lean, Spoerl Definition 21) says
that `κ` is an initial ordinal and that for every Sigma-one-star correct `γ` with `κ ∈ γ` and
every `a ∈ V_γ` there are `δ ∈ κ` Sigma-one-star correct, `x ∈ V_δ` and an elementary
`e : V_{δ+1} → V_{γ+1}` with a critical point `c` satisfying `e ‘ c = κ` and `e ‘ x = a`.

Under choice this is Magidor's characterization of supercompactness (Magidor 1971, Lemma 3.1;
Bagaria, C(n)-cardinals, the form quoted before Theorem 4.3): `κ` is supercompact iff every
large enough stage admits such a small embedding whose critical point is sent to `κ`.

Which half of that equivalence the project has: neither, as an equivalence. The project takes
the small-embedding statement as the definition of supercompactness in ZF. There is no
ultrapower construction and no normal fine measure in the repository, so the passage from small
embeddings to normal fine measures on `P_κ(λ)`, which is the ZFC content of Magidor's lemma, is
not formalized, and nothing here derives `IsWoodinSupercompact` from a measure-theoretic
definition. What the project does have around the definition is a supply of witnesses
(`IsCnExtendible.woodinSupercompact` in CnExtendibleWoodinSupercompact.lean produces them from
a fixed finite level of C(n)-extendibility), a normal form for the witnesses
(`woodinSupercompact_iff_highCritical` in WoodinSupercompactHighCritical.lean, which pushes the
critical point above any prescribed `α ∈ κ`), and the size consequences
(`IsWoodinSupercompact.regular`, `.inaccessible` in WoodinSupercompactInaccessible.lean).

## Comparison with the choiceless supercompactness notions

The repository also has `IsChoicelessSupercompact n` (ZFVP/SetTheory/FullChoicelessCardinals.lean)
built from `IsAlphaChoicelessSupercompact n α γ` and `ChoicelessSupercompactWitness n α γ μ a`
(ZFVP/SetTheory/ChoicelessSupercompact.lean). Neither implication between it and
`IsWoodinSupercompact` is a matter of unfolding, so none is proved here. The definitions differ
in three places.

* Correctness level. `IsChoicelessSupercompact n κ` quantifies over all `μ` with `Cn n μ` and
  `κ ∈ μ`; `IsWoodinSupercompact κ` quantifies over all Sigma-one-star correct `γ` with `κ ∈ γ`.
  `Cn.sigmaOneStarCorrect` (SigmaOneStarUnbounded.lean) turns `Cn sigmaOneStarCorrectnessBound`
  into Sigma-one-star correctness, and `IsSigmaOneStarCorrect` only returns `Cn 1` in that
  direction. So neither class of target ordinals contains the other for a given `n`: going from
  the choiceless notion to the Woodin notion needs a Sigma-one-star correct `γ` to be `Cn n`,
  and going back needs a `Cn n` ordinal to be Sigma-one-star correct. `Cn.of_le` does not close
  either gap.

* Rank of the embedding. `ChoicelessSupercompactWitness` asks for
  `e : V_ν → V_μ` with `ν ∈ γ`; `WoodinSupercompactWitness` asks for
  `e : V_{δ+1} → V_{γ+1}`, one rank higher on both sides, and a successor rank is not `Cn n`.

* Critical value. `ChoicelessSupercompactWitness n α γ μ a` only requires the critical point `c`
  to satisfy `α ∈ c`; it says nothing about `e ‘ c`. `WoodinSupercompactWitness κ γ a` requires
  `e ‘ c = κ`, which is the clause carrying Magidor's "critical point sent to `κ`". The Woodin
  side is strictly more informative on this clause: it also gives `α ∈ c` for every prescribed
  `α ∈ κ`, by `IsWoodinSupercompact.highCritical`. That is recorded below as
  `IsWoodinSupercompact.magidorEmbedding`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Magidor form of the small embeddings given by `IsWoodinSupercompact κ`: for a
Sigma-one-star correct `γ` above `κ`, a target `a ∈ V_γ` and a prescribed `α ∈ κ`, the witness
can be chosen with critical point `c` above `α` and with `e ‘ c = κ`. -/
theorem IsWoodinSupercompact.magidorEmbedding {κ γ a α : V} (hκ : IsWoodinSupercompact κ)
    (hκγ : κ ∈ γ) (hγ : IsSigmaOneStarCorrect γ) (ha : a ∈ hierarchy γ) (hα : α ∈ κ) :
    ∃ δ ∈ κ, IsSigmaOneStarCorrect δ ∧ ∃ x ∈ hierarchy δ, ∃ e,
      IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ γ)) e ∧
      ∃ c, IsCriticalPoint (hierarchy (succ δ)) e c ∧ α ∈ c ∧ e ‘ c = κ ∧ e ‘ x = a := by
  obtain ⟨_, δ, hδκ, hδ, x, hx, e, he, c, hc, hcκ, hxa, hαc⟩ :=
    hκ.highCritical.2.2 γ hκγ hγ a ha α hα
  exact ⟨δ, hδκ, hδ, x, hx, e, he, c, hc, hαc, hcκ, hxa⟩

/-- The size facts proved elsewhere about a Woodin supercompact cardinal, in one statement. -/
theorem IsWoodinSupercompact.size {κ : V} (hκ : IsWoodinSupercompact κ) :
    IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧ IsRegularCardinal κ ∧ IsChoicelessInaccessible κ :=
  ⟨hκ.1, hκ.omega_lt, hκ.regular, hκ.inaccessible⟩

end ZFVP
