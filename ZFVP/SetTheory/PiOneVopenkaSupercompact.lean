import ZFVP.SetTheory.PiOneVopenkaMagidorUnconditional
import ZFVP.SetTheory.MagidorVopenkaForward

/-! # Bagaria's Theorem 4.3(2) at `n = 1`, both directions

Bagaria, *C(n)-cardinals*, Theorem 4.3(2) says that the `Pi_n` fragment of Vopenka's principle
is equivalent to the existence of a proper class of `C(n)`-supercompact cardinals. This module
collects what the project proves at `n = 1`: the two directions as named theorems, the
unconditional sandwich they give, and the equivalence with the one remaining gap written as a
hypothesis.

Supercompactness is taken throughout in Magidor's small-embedding form `IsMagidorSupercompact`:
`κ` is an ordinal and every rank `V_γ` with `γ` above `κ` is the target of an elementary
`e : V_lb → V_γ` with `lb ∈ κ` whose critical point is sent to `κ` (Magidor 1971, quoted as
Lemma 3.1 in Bagaria section 3). That is the form Bagaria's arguments use. Its equivalence with
the definition by a `κ`-complete normal fine measure on `P_κ(γ)`, which is `IsSupercompact` in
`ZFVP.SetTheory.SupercompactMeasure`, is half formalized: `IsMagidorSupercompact.isSupercompact`
in `ZFVP.SetTheory.MagidorSupercompactMeasure` reads a measure off a small embedding, and
`ZFVP.SetTheory.SupercompactUltrapower` builds the ultrapower of a rank stage by a measure, with
a coded elementary `j : V_θ → M` of critical point `κ` and `M` closed under `lam`-indexed
families. What is still missing for the converse is the reflection step from `M` back to `V`,
which needs coded satisfaction to be absolute between a transitive `M` and `V`.

The reverse direction, `pi_one_vopenka_implies_unbounded_magidorSupercompact`, is unconditional
apart from internal choice. It is proved in `ZFVP.SetTheory.PiOneVopenkaMagidorUnconditional`.
The index of its `Pi_1` class is the least limit point of the closure points of the failure
function, not Bagaria's least limit ordinal above the marker; that choice is what makes one step
of the embedding reach the failure stage and removes the need for finite iterates. Kunen's
theorem sits inside it, in `criticalPoint_isMagidorClosurePoint`: it forces the critical sequence
to climb above the least closure point over an escaping failure stage, which is how the critical
point is shown to be a closure point. Internal choice is used there.

The forward direction, `unbounded_correctHighCriticalMagidorSupercompact_implies_pi_one_vopenka`,
needs more than the plain predicate. Its hypothesis is
`IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound`, which asks for the same
small embeddings and adds two clauses: the critical point can be pushed above any prescribed
ordinal of `κ`, and the source rank is a `C(n+1)` stage. The first fixes the parameters of a
Vopenka instance under the embedding, the second makes the source rank compute the syntax
dictionary and the class formula correctly. Neither follows from `IsMagidorSupercompact` as
stated; getting them is the ultrapower half of Magidor's characterization, which needs the
measure definition.

So the two directions do not close into an equivalence on their own, and
`pi_one_vopenka_iff_unbounded_magidorSupercompact` carries the missing step as the hypothesis
`hstrengthen`: a proper class of plain Magidor supercompact cardinals gives a proper class of
strengthened ones. What is proved without hypotheses is the sandwich
`pi_one_vopenka_between_magidorSupercompact_hypotheses`: the strengthened predicate unbounded
implies the `Pi_1` Vopenka scheme, which implies the plain predicate unbounded.

The two extra clauses cannot simply be moved into the reverse direction to close the loop. The
reverse direction produces its cardinal from a `Pi_1` class whose members are bounded objects,
and `C(n+1)` correctness of a stage is not a bounded condition: as
`ZFVP.SetTheory.PiOneCorrectStage` records, the antecedent `V_α ⊆ A` of the hierarchy graph is
`Pi_1` with no `Sigma_1` form in ZF, so `Cn 1` is not available at the `Pi_1` level the class
formula needs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Bagaria, Theorem 4.3(2) at `n = 1`, reverse direction: the `Pi_1` fragment of Vopenka's
principle gives a proper class of Magidor supercompact cardinals. Proved unconditionally in
`ZFVP.SetTheory.PiOneVopenkaMagidorUnconditional`; internal choice is used inside. -/
theorem pi_one_vopenka_implies_unbounded_magidorSupercompact (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ :=
  magidorSupercompact_unbounded_of_pi_one_vopenka hAC hVP

/-- Bagaria, Theorem 4.3(2) at `n = 1`, forward direction: a proper class of Magidor
supercompact cardinals in the strengthened sense, with a critical point above any prescribed
ordinal and a `C(n+1)` source stage, gives every `Pi_1` instance of the Vopenka scheme. Proved
in `ZFVP.SetTheory.MagidorVopenkaForward`. -/
theorem unbounded_correctHighCriticalMagidorSupercompact_implies_pi_one_vopenka
    (hM : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
      IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula 1 φ) : VopenkaInstance (V := V) φ :=
  magidorSupercompact_unbounded_implies_pi_one_vopenka hM φ hφ

/-- What the project proves outright at `n = 1`, with no open hypothesis beyond internal choice:
a proper class of strengthened Magidor supercompact cardinals implies the `Pi_1` Vopenka scheme,
and the `Pi_1` Vopenka scheme implies a proper class of plain Magidor supercompact cardinals.
The gap between the two predicates is the ultrapower half of Magidor's characterization. -/
theorem pi_one_vopenka_between_magidorSupercompact_hypotheses (hAC : InternalChoice V) :
    (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
        IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound κ) →
      (∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) ∧
        ((∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) →
          ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ) :=
  fun hM ↦ ⟨unbounded_correctHighCriticalMagidorSupercompact_implies_pi_one_vopenka hM,
    fun hVP ↦ pi_one_vopenka_implies_unbounded_magidorSupercompact hAC hVP⟩

/-- Bagaria, Theorem 4.3(2) at `n = 1`, as an equivalence, with the one unformalized step named:
`hstrengthen` says that a proper class of plain Magidor supercompact cardinals gives a proper
class of strengthened ones. Under it, the `Pi_1` Vopenka scheme is equivalent to a proper class
of Magidor supercompact cardinals. -/
theorem pi_one_vopenka_iff_unbounded_magidorSupercompact (hAC : InternalChoice V)
    (hstrengthen : (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ) →
      ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
        IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound κ) :
    (∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) ↔
      (∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ) :=
  ⟨fun hVP ↦ pi_one_vopenka_implies_unbounded_magidorSupercompact hAC hVP,
    fun hM ↦ unbounded_correctHighCriticalMagidorSupercompact_implies_pi_one_vopenka
      (hstrengthen hM)⟩

end ZFVP
