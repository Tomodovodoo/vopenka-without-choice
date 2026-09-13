import ZFVP.SetTheory.DomainTwoMarkerRankClass
import ZFVP.SetTheory.MagidorFailureClassFormula
import ZFVP.SetTheory.MagidorLemmaThreeOne
import ZFVP.SetTheory.FormulaFamilyRank

/-! # The `Pi_1` case of Bagaria's Theorem 4.3(2)

Bagaria, *C(n)-cardinals*, Theorem 4.3(2): the `Pi_1` fragment of Vopenka's principle implies
that there is a proper class of supercompact cardinals. Supercompactness is taken here in
Magidor's small-embedding form `IsMagidorSupercompact κ`: for every ordinal `γ` above `κ` there
are `lb ∈ κ` and an elementary `e : V_lb → V_γ` whose critical point is sent to `κ`. That is the
characterization Bagaria uses, and it is the one this project has.

The proof is by contradiction. Suppose no cardinal above `ξ` is Magidor supercompact. Then for
every ordinal `r` above `ξ` there is a least limit ordinal `lam` above `r` at which the whole
interval `succ ξ ⊆ ν ⊆ r` fails to be supercompact up to `lam`
(`ZFVP.SetTheory.MagidorFailureStages`). The structures `⟨V_{lam+ω}, ∈, ξ-constants, lam, r⟩`
for those pairs form a proper class, and the class is `Pi_1`: its side condition
`magidorFailureSideFormula` has every quantifier bounded by `lam` or by the domain `V_{lam+ω}`,
and the supercompactness clauses use the bounded formula `boundedMagidorSupercompactAtFormula`
rather than the predicate, so the side condition is a bounded statement about the domain. This is
why the class machine of `ZFVP.SetTheory.DomainTwoMarkerRankClass` hands the side condition the
domain as a fourth argument.

Vopenka's principle for that class gives an elementary `f : V_{lam+ω} → V_{lam'+ω}` between two
members with a critical point `κ` trapped between `succ ξ` and the marker `r`. Magidor's Lemma
3.1 (`ZFVP.SetTheory.MagidorLemmaThreeOne`) turns `f` into `IsMagidorSupercompactUpTo κ lam`,
which contradicts the minimality of `lam`. Kunen's theorem enters inside that lemma: it is what
forces the critical sequence of `f` to pass above every ordinal of `lam`.

`MagidorIterationReach` below is the one step of Lemma 3.1 that is still open. Bagaria composes
the finite iterates `j^m` of the embedding without comment; here `f ‘ x` need not lie back in the
source stage, so the composite is not available in general. The two cases that are proved are
`lam` closed under `f` and `lam ⊆ f ‘ κ`, and `MagidorIterationReach` packages exactly the
disjunction of those two, under exactly the data the class machine delivers. See
`ZFVP/SetTheory/MagidorLemmaThreeOne.lean` for the discussion of the missing case.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The open step of Magidor's Lemma 3.1: for the embeddings that the `Pi_1` class machine
produces, one of the two cases handled in `ZFVP.SetTheory.MagidorLemmaThreeOne` applies. The
hypotheses are exactly the data delivered by `pi_vopenka_domainTwoMarkerRank_embedding`
(including the marker equation `f ‘ lam = lam'`), and the conclusion is exactly the disjunction
that `magidorSupercompactUpTo_of_criticalPoint` consumes. -/
def MagidorIterationReach (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ lam lam' f κ : V, IsOrdinal lam → IsOrdinal lam' → IsLimitOrdinal lam → (ω : V) ∈ lam →
    IsLimitOrdinal lam' → (ω : V) ∈ lam' →
    IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f →
    IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ → κ ∈ lam →
    f ‘ lam = lam' → ((∀ δ ∈ lam, f ‘ δ ∈ lam) ∨ lam ⊆ f ‘ κ)

/-- The `Pi_1` fragment of Vopenka's principle gives a Magidor supercompact cardinal above every
ordinal `ξ` that contains `ω`. -/
theorem pi_one_vopenka_implies_magidorSupercompact_above (hAC : InternalChoice V)
    (hreach : MagidorIterationReach V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ)
    {ξ : V} [IsOrdinal ξ] (hωξ : (ω : V) ⊆ ξ) :
    ∃ κ : V, ξ ∈ κ ∧ IsMagidorSupercompact κ := by
  by_contra hcon
  have hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ := fun κ hκ hM ↦ hcon ⟨κ, hκ, hM⟩
  have hF : (formulaFamily membershipLanguageCode ∅ : V) ∈
      hierarchy (ordinalAdd (ω : V) (ω : V)) := formulaFamily_mem_hierarchy_omega_two
  -- `ω ∈ succ ξ`, the base of the class.
  have hωρ : (ω : V) ∈ succ ξ := by
    rcases IsOrdinal.subset_iff.mp hωξ with he | hlt
    · exact he ▸ mem_succ_self ξ
    · exact mem_succ_iff.mpr (Or.inr hlt)
  obtain ⟨lam, lam', r, r', f, κ, hlamord, hlam'ord, -, hρlam, hrlam, hψ,
      hρlam', hr'lam', hψ', hf, hflam, -, -, hκ, hρκ, hκr⟩ :=
    pi_vopenka_domainTwoMarkerRank_embedding (V := V) Nat.one_pos hVP
      magidorFailureSideFormula magidorFailureSideFormula_piOne (succ ξ) hωρ
      (magidorFailureSideFormula_functional hF)
      (magidorFailureSideFormula_unbounded hF hno)
  have : IsOrdinal lam := hlamord
  have : IsOrdinal lam' := hlam'ord
  obtain ⟨-, hlim, -, hleast⟩ := magidorFailureSideFormula_sound hF hψ
  obtain ⟨-, hlim', -, -⟩ := magidorFailureSideFormula_sound hF hψ'
  have hκord : IsOrdinal κ := hκ.ordinal
  have : IsOrdinal κ := hκord
  have hrord : IsOrdinal r := IsOrdinal.of_mem hrlam
  -- `ω` lies in `lam` and in `lam'` because the base `succ ξ` does.
  have hωlam : (ω : V) ∈ lam := hρlam _ hωρ
  have hωlam' : (ω : V) ∈ lam' := hρlam' _ hωρ
  -- `κ ⊆ r ∈ lam` puts `κ` in `lam`.
  have hκlam : κ ∈ lam := by
    rcases IsOrdinal.subset_iff.mp hκr with he | hlt
    · exact he ▸ hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  -- Magidor's Lemma 3.1, in the cases where the iterates of `f` are available.
  have hup : IsMagidorSupercompactUpTo κ lam :=
    magidorSupercompactUpTo_of_criticalPoint hlim hωlam hlim' hωlam' hF hf hκ hAC
      (hreach lam lam' f κ hlamord hlam'ord hlim hωlam hlim' hωlam' hf hκ hκlam hflam)
  exact not_magidorSupercompactUpTo_of_leastLimit hleast hκord hρκ hκr hup

/-- The `Pi_1` fragment of Vopenka's principle gives a proper class of Magidor supercompact
cardinals. This is Bagaria's Theorem 4.3(2) for `n = 1`. -/
theorem pi_one_vopenka_implies_magidorSupercompact_unbounded (hAC : InternalChoice V)
    (hreach : MagidorIterationReach V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ := by
  intro α hα
  have : IsOrdinal α := hα
  have hξord : IsOrdinal (α ∪ (ω : V)) := ordinal_union_isOrdinal α (ω : V)
  have : IsOrdinal (α ∪ (ω : V)) := hξord
  have hωξ : (ω : V) ⊆ α ∪ (ω : V) := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
  have hαξ : α ⊆ α ∪ (ω : V) := fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
  obtain ⟨κ, hκ, hM⟩ :=
    pi_one_vopenka_implies_magidorSupercompact_above hAC hreach hVP (ξ := α ∪ (ω : V)) hωξ
  have : IsOrdinal κ := hM.1
  refine ⟨κ, ?_, hM⟩
  rcases IsOrdinal.subset_iff.mp hαξ with he | hlt
  · exact he ▸ hκ
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hκ

end ZFVP
