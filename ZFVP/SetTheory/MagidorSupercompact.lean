import ZFVP.SetTheory.WoodinSupercompactMagidor
import ZFVP.SetTheory.GroundUniqueness

/-! # Magidor's small-embedding predicate

`IsMagidorSupercompactAt κ γ` says that there is a stage `V_β` with `β ∈ κ`, an ordinal `α ∈ β`
and an elementary embedding `e : V_β → V_γ` for the membership language whose critical point is
`α` and which sends `α` to `κ`. `IsMagidorSupercompact κ` says that `κ` is an ordinal and that
this holds for every ordinal `γ` above `κ`. The quantifier is written with an explicit
`IsOrdinal γ` hypothesis; the classical statement "for every `λ` above `κ`" means the same
thing, since the target of the embedding is the rank `V_γ` and only ordinals index ranks.

Under choice this is Magidor's characterization of supercompactness: `κ` is supercompact iff
every large enough rank is the target of such a small embedding whose critical point goes to `κ`
(Magidor 1971; quoted as Lemma 3.1 in Bagaria, *C(n)-cardinals*, section 3).

Bagaria's own arguments use the measure definition, a `κ`-complete normal fine ultrafilter on
`P_κ(γ)`, which the project now has as `IsSupercompact` in `ZFVP.SetTheory.SupercompactMeasure`.
One half of the passage between the two definitions is formalized:
`IsMagidorSupercompact.isSupercompact` in `ZFVP.SetTheory.MagidorSupercompactMeasure` reads a
measure off a small embedding. The other half runs through the ultrapower of a rank stage by such
a measure; that ultrapower is built in `ZFVP.SetTheory.SupercompactUltrapower`, which gives a
transitive `M`, a coded elementary `j : V_θ → M` with critical point `κ`, and closure of `M`
under families indexed by `lam`. Turning that into a small embedding needs one further step, the
reflection of "there is a small embedding into `V_γ` with critical point sent to `κ`" from `M`
back to `V`, which needs the coded satisfaction predicate to be absolute between `M` and `V`.
That step is not formalized, so `IsMagidorSupercompact κ → IsSupercompact κ` holds in the project
and the converse does not yet.

Link to the project's own predicate. `IsWoodinSupercompact` (Spoerl Definition 21) is a stronger
and more particular statement: it quantifies only over Sigma-one-star correct `γ`, but for such
`γ` it produces an embedding `V_{δ+1} → V_{γ+1}` with `δ ∈ κ` Sigma-one-star correct together
with a preimage for a prescribed `a ∈ V_γ`. The cheap half of the comparison is proved below as
`IsWoodinSupercompact.magidorSupercompactAt`: dropping the extra data from a Woodin witness at a
Sigma-one-star correct `γ` leaves exactly a Magidor witness at `succ γ`, with `β := succ δ` and
`α := c` the critical point. The full implication `IsWoodinSupercompact κ → IsMagidorSupercompact κ`
does not follow this way. The Magidor predicate asks for a witness at every ordinal `γ` above
`κ`, while the Woodin definition only answers at ordinals of the form `succ γ` for `γ`
Sigma-one-star correct. Filling the gap needs a way to move a witness from one target rank to
another, either by reflecting an arbitrary `γ` down to a Sigma-one-star correct one and
restricting the embedding, or by the ultrapower argument the project does not have.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A small embedding into `V_γ` whose critical point is sent to `κ`. -/
def IsMagidorSupercompactAt (κ γ : V) : Prop :=
  ∃ lb ∈ κ, ∃ ab ∈ lb, ∃ e, IsCodedMembershipEmbedding (hierarchy lb) (hierarchy γ) e ∧
    IsCriticalPoint (hierarchy lb) e ab ∧ e ‘ ab = κ

/-- Magidor's small-embedding predicate: a small embedding into every rank above `κ`. -/
def IsMagidorSupercompact (κ : V) : Prop :=
  IsOrdinal κ ∧ ∀ γ, IsOrdinal γ → κ ∈ γ → IsMagidorSupercompactAt κ γ

/-- The predicate restricted to target ranks below `lam`. -/
def IsMagidorSupercompactUpTo (κ lam : V) : Prop :=
  ∀ γ ∈ lam, IsOrdinal γ → κ ∈ γ → IsMagidorSupercompactAt κ γ

instance isMagidorSupercompactAt_definable : ℒₛₑₜ-relation[V] IsMagidorSupercompactAt := by
  unfold IsMagidorSupercompactAt
  definability

instance isMagidorSupercompact_definable : ℒₛₑₜ-predicate[V] IsMagidorSupercompact := by
  unfold IsMagidorSupercompact
  definability

instance isMagidorSupercompactUpTo_definable : ℒₛₑₜ-relation[V] IsMagidorSupercompactUpTo := by
  unfold IsMagidorSupercompactUpTo
  definability

theorem IsMagidorSupercompact.ordinal {κ : V} (hκ : IsMagidorSupercompact κ) : IsOrdinal κ := hκ.1

/-- Shrinking the bound keeps the bounded form. -/
theorem IsMagidorSupercompactUpTo.mono {κ lam lam' : V} (h : IsMagidorSupercompactUpTo κ lam')
    (hsub : lam ⊆ lam') : IsMagidorSupercompactUpTo κ lam :=
  fun γ hγ ↦ h γ (hsub γ hγ)

/-- The unbounded predicate gives the bounded one at every bound. -/
theorem IsMagidorSupercompact.upTo {κ : V} (hκ : IsMagidorSupercompact κ) (lam : V) :
    IsMagidorSupercompactUpTo κ lam :=
  fun γ _ hγ hκγ ↦ hκ.2 γ hγ hκγ

/-- A Woodin supercompactness witness at a Sigma-one-star correct `γ` is a Magidor witness at
`succ γ`: the source rank `V_{δ+1}` has `δ + 1 ∈ κ` because `κ` is an infinite initial ordinal,
and the critical point is an ordinal of `V_{δ+1}`, hence an element of `δ + 1`. -/
theorem IsWoodinSupercompact.magidorSupercompactAt {κ γ : V} (hκ : IsWoodinSupercompact κ)
    (hκγ : κ ∈ γ) (hγ : IsSigmaOneStarCorrect γ) : IsMagidorSupercompactAt κ (succ γ) := by
  let := hκ.1.1
  let := hγ.1.ordinal
  have hzγ : (∅ : V) ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr
    (IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ (ω : V) by simp) hγ.1.omega_lt)
  obtain ⟨_, δ, hδκ, hδ, _, _, e, he, c, hc, hec, _⟩ := hκ.2 γ hκγ hγ ∅ hzγ
  let := hδ.1.ordinal
  let := hc.ordinal
  refine ⟨succ δ, ?_, c, ?_, e, he, hc, hec⟩
  · exact succ_mem_of_initial hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.omega_lt) hδκ
  · exact ordinal_mem_hierarchy_iff.mp hc.mem_domain

end ZFVP
