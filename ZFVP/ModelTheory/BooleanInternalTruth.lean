import ZFVP.ModelTheory.LevyOrbitHomogeneity
import ZFVP.ModelTheory.LocalAtomicTruth

/-! The atomic truth lemma for a filter that lives inside the extension.

The repository proves the truth lemma for the external generic of a `ForcingContext`. Orbit
filters are sets of the extension, so nothing external is available for them: all that is known
is that they are antichain-generic ultrafilters on the checked regular sets
(`IsAntichainGeneric`, the five clauses of `IsOrbitFilter`).

This module runs the truth lemma for such a filter `U`. The induction on names is not redone
here: `local_atomicEquality_sound` and `local_atomicMembership_sound` already carry it out
inside any model of ZF, from three hypotheses about a filter on a poset. So the work is to
supply those hypotheses inside `A.Model` for the poset `(booleanConditions A.P A.R)ˇ` ordered by
`(booleanOrder A.P A.R)ˇ` and the filter `U`:

* `U` is a forcing filter on the checked completion (`antichainGeneric_isForcingFilter`);
* `U` meets the check of every subset of the completion that is dense in the ground model
  (`antichainGeneric_meets_check_dense`), because such a subset contains a maximal antichain
  and `U` meets every checked maximal antichain;
* from that, the witness clause `HasAtomicMembershipWitnesses` and the decision clause
  `HasAtomicEqualityDecisions` for the checked names.

Everything about names then transports along `A.checkEmbedding`, which sends `atomicMembership`,
`atomicEquality` and `regularJoin` computed in `V` to the same operations computed in `A.Model`
on the checked poset.

The payoff is `reductValues_of_antichainGeneric`: the hypothesis `ForcingContext.ReductValues`
of `solovayOrbitUnion_subset_booleanReal_of_algebra` holds for every antichain-generic
ultrafilter, so it is no longer an open assumption for orbit filters. It comes out as an
equality of values, not just the inclusion that `ReductValues` asks for. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A union of two subname-closed sets is subname-closed. -/
theorem IsSubnameClosed.union {N N' : V} (hN : IsSubnameClosed N) (hN' : IsSubnameClosed N') :
    IsSubnameClosed (N ∪ N') := by
  intro τ hτ ν hν
  rcases mem_union_iff.mp hτ with h | h
  · exact mem_union_iff.mpr (Or.inl (hN τ h ν hν))
  · exact mem_union_iff.mpr (Or.inr (hN' τ h ν hν))

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### The checked completion as a poset of the extension -/

/-- The checked Boolean completion is a forcing preorder of the extension. -/
theorem checkBool_preorder (A : ForcingContext V) :
    IsForcingPreorder (A.check (booleanConditions A.P A.R)) (A.check (booleanOrder A.P A.R)) :=
  A.checkEmbedding.map_forcingPreorder (booleanOrder_poset A.P A.R).1

theorem check_atomicMembership (A : ForcingContext V) (P R σ τ : V) :
    A.check (atomicMembership P R σ τ) =
      atomicMembership (A.check P) (A.check R) (A.check σ) (A.check τ) :=
  A.checkEmbedding.map_atomicMembership P R σ τ

theorem check_atomicEquality (A : ForcingContext V) (P R σ τ : V) :
    A.check (atomicEquality P R σ τ) =
      atomicEquality (A.check P) (A.check R) (A.check σ) (A.check τ) :=
  A.checkEmbedding.map_atomicEquality P R σ τ

theorem check_atomicEqualityDecisions (A : ForcingContext V) (P R σ τ : V) :
    A.check (atomicEqualityDecisions P R σ τ) =
      atomicEqualityDecisions (A.check P) (A.check R) (A.check σ) (A.check τ) :=
  A.checkEmbedding.map_atomicEqualityDecisions P R σ τ

/-- The reduct of a name is a name over the completion. -/
theorem nameReduct_isForcingName_completion (A : ForcingContext V) (τ : V) :
    IsForcingName (booleanConditions A.P A.R) (nameReduct A.P A.R τ) :=
  isForcingName_mono (fun _ hz ↦ (mem_inter_iff.mp hz).2)
    (nameReduct_isForcingName A.order
      (fun μ _ ν _ ↦ (mem_regularSets_iff _ _ _).mpr (booleanValueBase_regular A.order ν μ)))

section

variable {U : A.Model}
  (hU : IsAntichainGeneric (A.check (regularSets A.P A.R))
    (A.check (boolMaximalAntichains A.P A.R)) U)

include hU

/-- Every member of an antichain-generic ultrafilter is the check of a Boolean condition. -/
theorem exists_booleanConditions_of_mem {u : A.Model} (hu : u ∈ U) :
    ∃ u₀ ∈ booleanConditions A.P A.R, A.check u₀ = u := by
  obtain ⟨u₀, hu₀, rfl⟩ := (A.mem_check_iff _ _).mp (hU.subset u hu)
  refine ⟨u₀, (mem_booleanConditions_iff _ _ _).mpr
    ⟨(mem_regularSets_iff _ _ _).mp hu₀, ?_⟩, rfl⟩
  by_contra h
  apply hU.proper
  have he : u₀ = (∅ : V) :=
    mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ h, fun hz ↦ absurd hz not_mem_empty⟩)
  rw [← A.check_empty, ← he]
  exact hu

/-- A checked set in the filter is a Boolean condition. -/
theorem mem_booleanConditions_of_check_mem {u₀ : V} (h : A.check u₀ ∈ U) :
    u₀ ∈ booleanConditions A.P A.R := by
  obtain ⟨v₀, hv₀, he⟩ := exists_booleanConditions_of_mem hU h
  obtain rfl := (A.check_eq_iff _ _).mp he
  exact hv₀

theorem antichainGeneric_subset_checkBool :
    U ⊆ A.check (booleanConditions A.P A.R) := by
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := exists_booleanConditions_of_mem hU hu
  exact (A.check_mem_iff _ _).mpr hu₀

/-- An antichain-generic ultrafilter is a forcing filter on the checked completion. -/
theorem antichainGeneric_isForcingFilter (hAC : InternalChoice V) :
    IsForcingFilter (A.check (booleanConditions A.P A.R))
      (A.check (booleanOrder A.P A.R)) U := by
  refine ⟨antichainGeneric_subset_checkBool hU,
    ⟨A.check A.P, A.check_top_mem_of_antichainGeneric hAC hU⟩, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨q₀, hq₀, rfl⟩ := (A.mem_check_iff _ _).mp hq
    obtain ⟨p₀, hp₀, rfl⟩ := exists_booleanConditions_of_mem hU hp
    rw [← A.check_kpair, A.check_mem_iff] at hpq
    obtain ⟨-, -, hsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hpq
    exact hU.upward _ hp _ ((A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
      (booleanConditions_regular hq₀))) ((A.checkEmbedding.subset_iff _ _).mpr hsub)
  · intro p hp q hq
    obtain ⟨p₀, hp₀, rfl⟩ := exists_booleanConditions_of_mem hU hp
    obtain ⟨q₀, hq₀, rfl⟩ := exists_booleanConditions_of_mem hU hq
    have hin : A.check (p₀ ∩ q₀) ∈ U := by
      rw [A.check_inter]
      exact hU.inter _ hp _ hq
    have hinB : p₀ ∩ q₀ ∈ booleanConditions A.P A.R :=
      mem_booleanConditions_of_check_mem hU hin
    refine ⟨A.check (p₀ ∩ q₀), hin, ?_, ?_⟩
    · rw [← A.check_kpair, A.check_mem_iff]
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hinB, hp₀, fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · rw [← A.check_kpair, A.check_mem_iff]
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hinB, hq₀, fun z hz ↦ (mem_inter_iff.mp hz).2⟩

/-- An antichain-generic ultrafilter meets the check of every ground subset of the completion
that is dense for inclusion: the subset contains a maximal antichain of the completion. -/
theorem antichainGeneric_meets_check_dense (hAC : InternalChoice V) {D : V}
    (hD : D ⊆ booleanConditions A.P A.R)
    (hdense : ∀ b ∈ booleanConditions A.P A.R, ∃ d ∈ D, d ⊆ b) :
    ∃ d ∈ D, A.check d ∈ U := by
  obtain ⟨M, hM⟩ := exists_maximalAntichain (booleanOrder_poset A.P A.R).1 hD
    (wellOrderable_of_internalChoice hAC D)
  obtain ⟨a, ha, haU⟩ := hU.meets (A.check M)
    ((A.check_mem_iff _ _).mpr (maximalAntichainIn_dense_mem A.order hD hdense hM))
  obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
  exact ⟨a₀, hM.2.1 a₀ ha₀, haU⟩

/-- A checked join in the filter has a checked member of the family in the filter. -/
theorem antichainGeneric_check_join_mem (hAC : InternalChoice V) {Y : V}
    (hY : ∀ y ∈ Y, IsForcingRegular A.P A.R y)
    (h : A.check (regularJoin A.P A.R Y) ∈ U) : ∃ y ∈ Y, A.check y ∈ U := by
  obtain ⟨M, hM, href⟩ := exists_refining_antichain hAC A.order hY
  obtain ⟨a, ha, haU⟩ := hU.meets (A.check M) ((A.check_mem_iff _ _).mpr hM)
  obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
  rcases href a₀ ha₀ with ⟨y, hy, hay⟩ | hneg
  · exact ⟨y, hy, hU.upward _ haU _ ((A.check_mem_iff _ _).mpr
      ((mem_regularSets_iff _ _ _).mpr (hY y hy))) ((A.checkEmbedding.subset_iff _ _).mpr hay)⟩
  · exfalso
    have hjoin : IsForcingRegular A.P A.R (regularJoin A.P A.R Y) :=
      regularJoin_regular A.order (fun y hy ↦ (hY y hy).1)
    have hin := hU.inter _ haU _ h
    rw [← A.check_inter] at hin
    have hempty : a₀ ∩ regularJoin A.P A.R Y = (∅ : V) := by
      apply mem_ext
      intro p
      refine ⟨fun hp ↦ ?_, fun hp ↦ absurd hp not_mem_empty⟩
      obtain ⟨hpa, hpj⟩ := mem_inter_iff.mp hp
      have : p ∈ regularJoin A.P A.R Y ∩ forcingNegation A.P A.R (regularJoin A.P A.R Y) :=
        mem_inter_iff.mpr ⟨hpj, hneg p hpa⟩
      rw [inter_forcingNegation_eq_empty A.order hjoin.1] at this
      exact absurd this not_mem_empty
    rw [hempty, A.check_empty] at hin
    exact hU.proper hin

/-! ### The two clauses of the local truth lemma -/

/-- The witness clause of the local truth lemma for the checked names: below a condition forcing
a membership the filter finds an actual witnessing pair of the name. -/
theorem antichainGeneric_membershipWitnesses (hAC : InternalChoice V) {N₀ : V}
    (hnames : ∀ τ ∈ N₀, ∀ z ∈ τ, ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ) :
    HasAtomicMembershipWitnesses (A.check (booleanConditions A.P A.R))
      (A.check (booleanOrder A.P A.R)) (A.check N₀) U := by
  have hB := (booleanOrder_poset A.P A.R).1
  intro σ hσ τ hτ p hp hpM
  obtain ⟨σ₀, hσ₀, rfl⟩ := (A.mem_check_iff _ _).mp hσ
  obtain ⟨τ₀, hτ₀, rfl⟩ := (A.mem_check_iff _ _).mp hτ
  obtain ⟨p₀, hp₀, rfl⟩ := exists_booleanConditions_of_mem hU hp
  rw [← A.check_atomicMembership, A.check_mem_iff] at hpM
  obtain ⟨-, htest⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hpM
  set D : V := sep (booleanConditions A.P A.R)
    (fun b ↦ (∃ ν : V, ∃ s : V, ⟨ν, s⟩ₖ ∈ τ₀ ∧ b ⊆ s ∧
        b ∈ atomicEquality (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ₀ ν) ∨
      (∀ z, z ∈ b → z ∉ p₀)) (by definability) with hDdef
  have hmemD : ∀ b : V, b ∈ D ↔ b ∈ booleanConditions A.P A.R ∧
      ((∃ ν : V, ∃ s : V, ⟨ν, s⟩ₖ ∈ τ₀ ∧ b ⊆ s ∧
        b ∈ atomicEquality (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ₀ ν) ∨
      (∀ z, z ∈ b → z ∉ p₀)) := fun b ↦ by rw [hDdef]; exact mem_sep_iff
  have hDsub : D ⊆ booleanConditions A.P A.R := fun b hb ↦ ((hmemD b).mp hb).1
  have hdense : ∀ b ∈ booleanConditions A.P A.R, ∃ d ∈ D, d ⊆ b := by
    intro c hc
    by_cases hcp : ∃ z : V, z ∈ c ∧ z ∈ p₀
    · obtain ⟨z, hzc, hzp⟩ := hcp
      have hcpB : c ∩ p₀ ∈ booleanConditions A.P A.R :=
        inter_mem_booleanConditions hc hp₀ (mem_inter_iff.mpr ⟨hzc, hzp⟩)
      have hord : (⟨c ∩ p₀, p₀⟩ₖ : V) ∈ booleanOrder A.P A.R :=
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr
          ⟨hcpB, hp₀, fun w hw ↦ (mem_inter_iff.mp hw).2⟩
      obtain ⟨r, hr, hrc, ν, s, hνs, hrs, he⟩ := htest (c ∩ p₀) hcpB hord
      obtain ⟨-, -, hrcsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hrc
      obtain ⟨-, -, hrssub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hrs
      exact ⟨r, (hmemD r).mpr ⟨hr, Or.inl ⟨ν, s, hνs, hrssub, he⟩⟩,
        fun w hw ↦ (mem_inter_iff.mp (hrcsub w hw)).1⟩
    · refine ⟨c, (hmemD c).mpr ⟨hc, Or.inr ?_⟩, subset_refl c⟩
      intro z hzc hzp
      exact hcp ⟨z, hzc, hzp⟩
  obtain ⟨b₀, hb₀D, hb₀U⟩ := antichainGeneric_meets_check_dense hU hAC hDsub hdense
  obtain ⟨hb₀B, hcase⟩ := (hmemD b₀).mp hb₀D
  rcases hcase with ⟨ν₀, s₀, hνs, hbs, he⟩ | hdisj
  · have hsB : s₀ ∈ booleanConditions A.P A.R := by
      obtain ⟨υ, q, hq, heq⟩ := hnames τ₀ hτ₀ _ hνs
      obtain ⟨-, rfl⟩ := kpair_iff.mp heq
      exact hq
    refine ⟨A.check b₀, hb₀U, A.check ν₀, A.check s₀, ?_, ?_, ?_⟩
    · rw [← A.check_kpair, A.check_mem_iff]
      exact hνs
    · exact hU.upward _ hb₀U _ ((A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
        (booleanConditions_regular hsB))) ((A.checkEmbedding.subset_iff _ _).mpr hbs)
    · rw [← A.check_atomicEquality, A.check_mem_iff]
      exact he
  · exfalso
    have hin := hU.inter _ hb₀U _ hp
    rw [← A.check_inter] at hin
    have hempty : b₀ ∩ p₀ = (∅ : V) := by
      apply mem_ext
      intro z
      refine ⟨fun hz ↦ ?_, fun hz ↦ absurd hz not_mem_empty⟩
      obtain ⟨hzb, hzp⟩ := mem_inter_iff.mp hz
      exact absurd hzp (hdisj z hzb)
    rw [hempty, A.check_empty] at hin
    exact hU.proper hin

/-- The decision clause of the local truth lemma for the checked names. -/
theorem antichainGeneric_equalityDecisions (hAC : InternalChoice V) (N₀ : V) :
    HasAtomicEqualityDecisions (A.check (booleanConditions A.P A.R))
      (A.check (booleanOrder A.P A.R)) (A.check N₀) U := by
  intro σ hσ τ hτ
  obtain ⟨σ₀, -, rfl⟩ := (A.mem_check_iff _ _).mp hσ
  obtain ⟨τ₀, -, rfl⟩ := (A.mem_check_iff _ _).mp hτ
  obtain ⟨hDsub, hdense⟩ :=
    atomicEqualityDecisions_dense (booleanOrder_poset A.P A.R).1 σ₀ τ₀
  have hdense' : ∀ b ∈ booleanConditions A.P A.R,
      ∃ d ∈ atomicEqualityDecisions (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ₀ τ₀,
        d ⊆ b := by
    intro b hb
    obtain ⟨q, hq, hqb⟩ := hdense b hb
    exact ⟨q, hq, ((kpair_mem_booleanOrder_iff _ _ _ _).mp hqb).2.2⟩
  obtain ⟨d, hd, hdU⟩ := antichainGeneric_meets_check_dense hU hAC hDsub hdense'
  refine ⟨A.check d, hdU, ?_⟩
  rw [← A.check_atomicEqualityDecisions, A.check_mem_iff]
  exact hd

/-! ### The truth lemma for checked names -/

/-- A condition of the completion in the filter that forces an equality of two checked names
makes their values at the filter equal. -/
theorem nameValue_check_eq_of_mem_atomicEquality (hAC : InternalChoice V) {N₀ : V}
    (hN₀ : IsSubnameClosed N₀)
    (hnames : ∀ τ' ∈ N₀, ∀ z ∈ τ', ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ)
    {σ τ p : V} (hσ : σ ∈ N₀) (hτ : τ ∈ N₀) (hpU : A.check p ∈ U)
    (hp : p ∈ atomicEquality (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ τ) :
    nameValue U (A.check σ) = nameValue U (A.check τ) :=
  local_atomicEquality_sound (checkBool_preorder A) (A.checkEmbedding.map_subnameClosed hN₀)
    (antichainGeneric_isForcingFilter hU hAC)
    (antichainGeneric_membershipWitnesses hU hAC hnames)
    ((A.check_mem_iff _ _).mpr hσ) ((A.check_mem_iff _ _).mpr hτ) hpU
    (by rw [← A.check_atomicEquality, A.check_mem_iff]; exact hp)

/-- A condition of the completion in the filter that forces a membership between two checked
names puts their values at the filter in that relation. -/
theorem nameValue_check_mem_of_mem_atomicMembership (hAC : InternalChoice V) {N₀ : V}
    (hN₀ : IsSubnameClosed N₀)
    (hnames : ∀ τ' ∈ N₀, ∀ z ∈ τ', ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ)
    {σ τ p : V} (hσ : σ ∈ N₀) (hτ : τ ∈ N₀) (hpU : A.check p ∈ U)
    (hp : p ∈ atomicMembership (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ τ) :
    nameValue U (A.check σ) ∈ nameValue U (A.check τ) :=
  local_atomicMembership_sound (checkBool_preorder A) (A.checkEmbedding.map_subnameClosed hN₀)
    (antichainGeneric_isForcingFilter hU hAC)
    (antichainGeneric_membershipWitnesses hU hAC hnames)
    ((A.check_mem_iff _ _).mpr hσ) ((A.check_mem_iff _ _).mpr hτ) hpU
    (by rw [← A.check_atomicMembership, A.check_mem_iff]; exact hp)

/-- The converse: a membership between the values of two checked names at the filter is forced by
some condition of the completion in the filter. -/
theorem exists_mem_atomicMembership_of_nameValue_check_mem (hAC : InternalChoice V) {N₀ : V}
    (hN₀ : IsSubnameClosed N₀) {σ τ : V} (hσ : σ ∈ N₀) (hτ : τ ∈ N₀)
    (h : nameValue U (A.check σ) ∈ nameValue U (A.check τ)) :
    ∃ p ∈ booleanConditions A.P A.R, A.check p ∈ U ∧
      p ∈ atomicMembership (booleanConditions A.P A.R) (booleanOrder A.P A.R) σ τ := by
  obtain ⟨p, hpU, hp⟩ := local_atomicMembership_truth (checkBool_preorder A)
    (A.checkEmbedding.map_subnameClosed hN₀) (antichainGeneric_isForcingFilter hU hAC)
    (antichainGeneric_equalityDecisions hU hAC N₀)
    ((A.check_mem_iff _ _).mpr hσ) ((A.check_mem_iff _ _).mpr hτ) h
  obtain ⟨p₀, hp₀, rfl⟩ := exists_booleanConditions_of_mem hU hpU
  rw [← A.check_atomicMembership, A.check_mem_iff] at hp
  exact ⟨p₀, hp₀, hpU, hp⟩

/-! ### The two statements about the Boolean values -/

/-- The atomic truth lemma for membership, in the form used by the orbit filters: if the filter
contains the checked Boolean value of `ν ∈ μ`, then the value of `ν` is a member of the value of
`μ`. -/
theorem check_mem_nameValue_of_booleanValueBase (hAC : InternalChoice V) {ν μ : V}
    (hμ : IsForcingName (booleanConditions A.P A.R) μ) (hν : ν ∈ domain μ)
    (h : A.check (booleanValueBase A.P A.R ν μ) ∈ U) :
    nameValue U (A.check ν) ∈ nameValue U (A.check μ) := by
  have hYreg : ∀ y ∈ atomicMembership (booleanConditions A.P A.R) (booleanOrder A.P A.R) ν μ,
      IsForcingRegular A.P A.R y := fun y hy ↦
    booleanConditions_regular (atomicMembership_subset _ _ _ _ y hy)
  obtain ⟨y, hy, hyU⟩ := antichainGeneric_check_join_mem hU hAC hYreg h
  exact nameValue_check_mem_of_mem_atomicMembership hU hAC (nameClosure_closed μ) hμ
    (nameClosure_closed μ μ (mem_nameClosure_self μ) ν hν) (mem_nameClosure_self μ) hyU hy

/-- The atomic truth lemma for equality: if the filter contains the checked Boolean value of
`ν = ν'`, the two names take the same value at the filter. -/
theorem nameValue_eq_of_atomicEquality (hAC : InternalChoice V) {ν ν' : V}
    (hν : IsForcingName (booleanConditions A.P A.R) ν)
    (hν' : IsForcingName (booleanConditions A.P A.R) ν')
    (h : A.check (regularJoin A.P A.R (atomicEquality (booleanConditions A.P A.R)
      (booleanOrder A.P A.R) ν ν')) ∈ U) :
    nameValue U (A.check ν) = nameValue U (A.check ν') := by
  have hYreg : ∀ y ∈ atomicEquality (booleanConditions A.P A.R) (booleanOrder A.P A.R) ν ν',
      IsForcingRegular A.P A.R y := fun y hy ↦
    booleanConditions_regular (atomicEquality_subset _ _ _ _ y hy)
  obtain ⟨y, hy, hyU⟩ := antichainGeneric_check_join_mem hU hAC hYreg h
  have hnames : ∀ τ' ∈ nameClosure ν ∪ nameClosure ν', ∀ z ∈ τ',
      ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ := by
    intro τ' hτ' z hz
    rcases mem_union_iff.mp hτ' with h' | h'
    · exact hν τ' h' z hz
    · exact hν' τ' h' z hz
  exact nameValue_check_eq_of_mem_atomicEquality hU hAC
    ((nameClosure_closed ν).union (nameClosure_closed ν')) hnames
    (mem_union_iff.mpr (Or.inl (mem_nameClosure_self ν)))
    (mem_union_iff.mpr (Or.inr (mem_nameClosure_self ν'))) hyU hy

/-- The converse of the membership direction: a membership between the values of two checked
names puts the checked Boolean value of that membership in the filter. -/
theorem booleanValueBase_mem_of_nameValue_check_mem (hAC : InternalChoice V) {ν μ : V}
    (hν : ν ∈ domain μ)
    (h : nameValue U (A.check ν) ∈ nameValue U (A.check μ)) :
    A.check (booleanValueBase A.P A.R ν μ) ∈ U := by
  obtain ⟨p, -, hpU, hp⟩ := exists_mem_atomicMembership_of_nameValue_check_mem hU hAC
    (nameClosure_closed μ) (nameClosure_closed μ μ (mem_nameClosure_self μ) ν hν)
    (mem_nameClosure_self μ) h
  exact hU.upward _ hpU _ ((A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
    (booleanValueBase_regular A.order ν μ)))
    ((A.checkEmbedding.subset_iff _ _).mpr (subset_booleanValueBase A.order hp))

/-- The atomic truth lemma for membership as an equivalence. -/
theorem check_mem_nameValue_iff (hAC : InternalChoice V) {ν μ : V}
    (hμ : IsForcingName (booleanConditions A.P A.R) μ) (hν : ν ∈ domain μ) :
    nameValue U (A.check ν) ∈ nameValue U (A.check μ) ↔
      A.check (booleanValueBase A.P A.R ν μ) ∈ U :=
  ⟨booleanValueBase_mem_of_nameValue_check_mem hU hAC hν,
    check_mem_nameValue_of_booleanValueBase hU hAC hμ hν⟩

/-! ### The reduct of a name -/

/-- A name and its reduct have the same value at an antichain-generic ultrafilter of the
extension. The reduct is forced equal to the name by every condition of the completion, and the
filter contains the checked top. -/
theorem nameValue_check_nameReduct_eq (hAC : InternalChoice V) {τ : V}
    (hτ : IsForcingName (booleanConditions A.P A.R) τ) :
    nameValue U (A.check (nameReduct A.P A.R τ)) = nameValue U (A.check τ) := by
  have hred := nameReduct_isForcingName_completion A τ
  have hnames : ∀ τ' ∈ nameClosure (nameReduct A.P A.R τ) ∪ nameClosure τ, ∀ z ∈ τ',
      ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ := by
    intro τ' hτ' z hz
    rcases mem_union_iff.mp hτ' with h' | h'
    · exact hred τ' h' z hz
    · exact hτ τ' h' z hz
  exact nameValue_check_eq_of_mem_atomicEquality hU hAC
    ((nameClosure_closed _).union (nameClosure_closed τ)) hnames
    (mem_union_iff.mpr (Or.inl (mem_nameClosure_self _)))
    (mem_union_iff.mpr (Or.inr (mem_nameClosure_self τ)))
    (A.check_top_mem_of_antichainGeneric hAC hU)
    (forcedEqual_nameReduct A.order τ A.P (top_mem_booleanConditions ⟨A.one, A.top.1⟩))

/-- Every antichain-generic ultrafilter of the extension satisfies `ReductValues`, the hypothesis
of `solovayOrbitUnion_subset_booleanReal_of_algebra`. -/
theorem reductValues_of_antichainGeneric (hAC : InternalChoice V) : A.ReductValues U := by
  intro τ hτ
  rw [nameValue_check_nameReduct_eq hU hAC hτ]

end

/-- An orbit filter satisfies `ReductValues`: only the first five clauses of `IsOrbitFilter` are
used, and they are exactly antichain-genericity. This discharges the hypothesis `hred` of
`solovayOrbitUnion_subset_booleanReal_of_algebra`. -/
theorem reductValues_of_isOrbitFilter (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H) :
    A.ReductValues H :=
  reductValues_of_antichainGeneric
    (antichainGeneric_of_clauses hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1) hAC

end ForcingContext

end ZFVP
