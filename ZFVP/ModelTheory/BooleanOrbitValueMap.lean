import ZFVP.ModelTheory.BooleanGenericAutomorphism

/-! The ground map of Jech, Set Theory, Lemma 25.5 (Karagila and Schilhan, Lemma 9.3) in the form
the development needs.

Let `H` be a filter of the extension on the checked Boolean completion satisfying the orbit
clauses, and let `τ` be a set of the ground model whose Boolean membership values decide `H` on
checked conditions: `b̌ ∈ H` exactly when the generic meets `‖b̌ ∈ τ‖`. Write `e b` for
`‖b̌ ∈ τ‖`, a regular subset of the ground poset, so that meets in the completion are
intersections and the order is inclusion.

`exists_orbitValue_condition` produces a single Boolean condition `p₀` met by the generic below
which `e` is a homomorphism: it is monotone, it takes intersections to intersections, it sends
the zero of the completion to zero, and it is above the top. This is the step of the classical
proof that turns the map `b ↦ ‖b̌ ∈ Ḣ‖` into a map of Boolean algebras, and it is what an
automorphism of the completion has to be built from.

The proof does not use the truth lemma for `τ`, so it does not need `τ` to be a forcing name of
the completion: each clause is obtained from a dense set of the completion, ground definable from
`τ`, whose conditions either satisfy the clause or force a counterexample to it, and the second
case is refuted by the clauses of the filter through the deciding property of `τ`. The dense sets
are met by the Boolean generic induced by `A.G`, so the conditions they produce are met by `A.G`,
and the four are intersected inside the generic filter.

`exists_orbitValue_condition_complete` adds the completeness clause: below the same kind of
condition, `e` sends every ground maximal antichain of the completion to a family whose join is
above the condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Regular sets, cones and the generic filter -/

/-- The Boolean value `‖b̌ ∈ τ‖` is a regular subset of the ground poset. -/
theorem booleanMemValue_regular (A : ForcingContext V) (τ b : V) :
    IsForcingRegular A.P A.R (A.booleanMemValue τ b) :=
  A.booleanValue_regular memAtom _

/-- The regular cone of a condition of the forcing negation of a regular set avoids that set. -/
theorem coneRegular_avoids {X q : V} (hX : IsForcingRegular A.P A.R X)
    (hq : q ∈ forcingNegation A.P A.R X) : ∀ t ∈ coneRegular A.P A.R q, t ∉ X := by
  intro t ht htX
  obtain ⟨htP, hh⟩ := mem_coneRegular_iff.mp ht
  obtain ⟨w, hwP, hwq, hwt⟩ := hh t htP (A.order.2.1 t htP)
  exact ((mem_forcingNegation_iff _ _ _ _).mp hq).2 w hwP hwq (hX.2.1 t htX w hwP hwt)

/-- A condition outside a regular set has an extension whose regular cone avoids the set. -/
theorem exists_cone_avoiding {X r : V} (hX : IsForcingRegular A.P A.R X) (hr : r ∈ A.P)
    (hrX : r ∉ X) :
    ∃ q ∈ A.P, ⟨q, r⟩ₖ ∈ A.R ∧ ∀ t ∈ coneRegular A.P A.R q, t ∉ X := by
  obtain ⟨q, hqn, hqr⟩ := exists_forcingNegation_of_not_mem hr hrX hX.2.2
  exact ⟨q, forcingNegation_subset _ _ _ q hqn, hqr, coneRegular_avoids hX hqn⟩

/-- The generic cannot meet both a regular set and a regular set avoiding it. -/
theorem meets_false_of_avoids {s X : V} (hs : IsForcingRegular A.P A.R s)
    (hX : IsForcingRegular A.P A.R X) (hsG : ∃ p ∈ A.G, p ∈ s) (hXG : ∃ p ∈ A.G, p ∈ X)
    (havoid : ∀ t ∈ s, t ∉ X) : False := by
  obtain ⟨p, hpG, hps⟩ := hsG
  obtain ⟨p', hp'G, hp'X⟩ := hXG
  obtain ⟨t, htG, htp, htp'⟩ := A.generic.1.2.2.2 p hpG p' hp'G
  have htP : t ∈ A.P := A.generic.1.1 t htG
  exact havoid t (hs.2.1 p hps t htP htp) (hX.2.1 p' hp'X t htP htp')

/-- Two regular sets met by the generic have an intersection met by the generic. -/
theorem meets_inter {s t : V} (hs : IsForcingRegular A.P A.R s) (ht : IsForcingRegular A.P A.R t)
    (hsG : ∃ p ∈ A.G, p ∈ s) (htG : ∃ p ∈ A.G, p ∈ t) : ∃ p ∈ A.G, p ∈ s ∩ t := by
  obtain ⟨p, hpG, hps⟩ := hsG
  obtain ⟨p', hp'G, hp't⟩ := htG
  obtain ⟨w, hwG, hwp, hwp'⟩ := A.generic.1.2.2.2 p hpG p' hp'G
  have hwP : w ∈ A.P := A.generic.1.1 w hwG
  exact ⟨w, hwG, mem_inter_iff.mpr ⟨hs.2.1 p hps w hwP hwp, ht.2.1 p' hp't w hwP hwp'⟩⟩

/-! ### The dense sets deciding the homomorphism clauses -/

/-- The Boolean conditions that either make `e` monotone below them or force a counterexample to
monotonicity. -/
noncomputable def orbitMonoSet (A : ForcingContext V) (τ : V) : V :=
  sep (booleanConditions A.P A.R)
    (fun s ↦
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
        ∀ r, r ∈ A.booleanMemValue τ b → r ∈ s → r ∈ A.booleanMemValue τ c) ∨
      (∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R, b ⊆ c ∧
        (∀ t ∈ s, t ∈ A.booleanMemValue τ b) ∧ (∀ t ∈ s, t ∉ A.booleanMemValue τ c)))
    (by
      have := A.booleanMemValue_definable τ
      definability)

theorem mem_orbitMonoSet_iff (A : ForcingContext V) (τ s : V) :
    s ∈ A.orbitMonoSet τ ↔ s ∈ booleanConditions A.P A.R ∧
      ((∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
        ∀ r, r ∈ A.booleanMemValue τ b → r ∈ s → r ∈ A.booleanMemValue τ c) ∨
      (∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R, b ⊆ c ∧
        (∀ t ∈ s, t ∈ A.booleanMemValue τ b) ∧ (∀ t ∈ s, t ∉ A.booleanMemValue τ c))) :=
  mem_sep_iff

theorem orbitMonoSet_dense (A : ForcingContext V) (τ : V) :
    ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) (A.orbitMonoSet τ) := by
  refine ⟨sep_subset, fun u hu ↦ ?_⟩
  by_cases hgood : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
      ∀ r, r ∈ A.booleanMemValue τ b → r ∈ u → r ∈ A.booleanMemValue τ c
  · exact ⟨u, (A.mem_orbitMonoSet_iff τ u).mpr ⟨hu, Or.inl hgood⟩,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  · obtain ⟨b, hb, c, hc, hbc, r, hrb, hru, hrc⟩ :
        ∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R, b ⊆ c ∧
          ∃ r, r ∈ A.booleanMemValue τ b ∧ r ∈ u ∧ r ∉ A.booleanMemValue τ c := by
      by_contra hcon
      refine hgood (fun b hb c hc hbc r hrb hru ↦ ?_)
      by_contra hrc
      exact hcon ⟨b, hb, c, hc, hbc, r, hrb, hru, hrc⟩
    have hureg := booleanConditions_regular hu
    have hbreg := A.booleanMemValue_regular τ b
    have hrP : r ∈ A.P := hbreg.1 r hrb
    obtain ⟨q, hqP, hqr, havoid⟩ := exists_cone_avoiding (A.booleanMemValue_regular τ c) hrP hrc
    have hqu : q ∈ u := hureg.2.1 r hru q hqP hqr
    have hqb : q ∈ A.booleanMemValue τ b := hbreg.2.1 r hrb q hqP hqr
    have hcone : coneRegular A.P A.R q ∈ booleanConditions A.P A.R :=
      coneRegular_mem_booleanConditions A.order hqP
    refine ⟨coneRegular A.P A.R q, (A.mem_orbitMonoSet_iff τ _).mpr ⟨hcone,
      Or.inr ⟨b, hb, c, hc, hbc, fun t ht ↦ ?_, havoid⟩⟩, ?_⟩
    · exact coneRegular_subset_of_mem A.order hbreg hqb t ht
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hcone, hu, coneRegular_subset_of_mem A.order hureg hqu⟩

/-- The Boolean conditions that either make `e` preserve intersections below them or force a
counterexample. -/
noncomputable def orbitInterSet (A : ForcingContext V) (τ : V) : V :=
  sep (booleanConditions A.P A.R)
    (fun s ↦
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, ∀ d, d = b ∩ c →
        ∀ r, r ∈ A.booleanMemValue τ b → r ∈ A.booleanMemValue τ c → r ∈ s →
          r ∈ A.booleanMemValue τ d) ∨
      (∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R, ∃ d, d = b ∩ c ∧
        (∀ t ∈ s, t ∈ A.booleanMemValue τ b) ∧ (∀ t ∈ s, t ∈ A.booleanMemValue τ c) ∧
        (∀ t ∈ s, t ∉ A.booleanMemValue τ d)))
    (by
      have := A.booleanMemValue_definable τ
      definability)

theorem mem_orbitInterSet_iff (A : ForcingContext V) (τ s : V) :
    s ∈ A.orbitInterSet τ ↔ s ∈ booleanConditions A.P A.R ∧
      ((∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, ∀ d, d = b ∩ c →
        ∀ r, r ∈ A.booleanMemValue τ b → r ∈ A.booleanMemValue τ c → r ∈ s →
          r ∈ A.booleanMemValue τ d) ∨
      (∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R, ∃ d, d = b ∩ c ∧
        (∀ t ∈ s, t ∈ A.booleanMemValue τ b) ∧ (∀ t ∈ s, t ∈ A.booleanMemValue τ c) ∧
        (∀ t ∈ s, t ∉ A.booleanMemValue τ d))) :=
  mem_sep_iff

theorem orbitInterSet_dense (A : ForcingContext V) (τ : V) :
    ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) (A.orbitInterSet τ) := by
  refine ⟨sep_subset, fun u hu ↦ ?_⟩
  by_cases hgood : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, ∀ d, d = b ∩ c →
      ∀ r, r ∈ A.booleanMemValue τ b → r ∈ A.booleanMemValue τ c → r ∈ u →
        r ∈ A.booleanMemValue τ d
  · exact ⟨u, (A.mem_orbitInterSet_iff τ u).mpr ⟨hu, Or.inl hgood⟩,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  · obtain ⟨b, hb, c, hc, r, hrb, hrc, hru, hrd⟩ :
        ∃ b ∈ booleanConditions A.P A.R, ∃ c ∈ booleanConditions A.P A.R,
          ∃ r, r ∈ A.booleanMemValue τ b ∧ r ∈ A.booleanMemValue τ c ∧ r ∈ u ∧
            r ∉ A.booleanMemValue τ (b ∩ c) := by
      by_contra hcon
      refine hgood (fun b hb c hc d hd r hrb hrc hru ↦ ?_)
      subst hd
      by_contra hrd
      exact hcon ⟨b, hb, c, hc, r, hrb, hrc, hru, hrd⟩
    have hureg := booleanConditions_regular hu
    have hbreg := A.booleanMemValue_regular τ b
    have hcreg := A.booleanMemValue_regular τ c
    have hrP : r ∈ A.P := hbreg.1 r hrb
    obtain ⟨q, hqP, hqr, havoid⟩ :=
      exists_cone_avoiding (A.booleanMemValue_regular τ (b ∩ c)) hrP hrd
    have hqu : q ∈ u := hureg.2.1 r hru q hqP hqr
    have hqb : q ∈ A.booleanMemValue τ b := hbreg.2.1 r hrb q hqP hqr
    have hqc : q ∈ A.booleanMemValue τ c := hcreg.2.1 r hrc q hqP hqr
    have hcone : coneRegular A.P A.R q ∈ booleanConditions A.P A.R :=
      coneRegular_mem_booleanConditions A.order hqP
    refine ⟨coneRegular A.P A.R q, (A.mem_orbitInterSet_iff τ _).mpr ⟨hcone,
      Or.inr ⟨b, hb, c, hc, b ∩ c, rfl, fun t ht ↦ ?_, fun t ht ↦ ?_, havoid⟩⟩, ?_⟩
    · exact coneRegular_subset_of_mem A.order hbreg hqb t ht
    · exact coneRegular_subset_of_mem A.order hcreg hqc t ht
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hcone, hu, coneRegular_subset_of_mem A.order hureg hqu⟩

/-! ### The condition below which the value map is a homomorphism -/

/-- The ground map of Jech, Set Theory, Lemma 25.5. For a filter `H` of the extension satisfying
the orbit clauses and a ground set `τ` whose Boolean membership values decide `H` on checked
conditions, there is one Boolean condition `p₀` met by the generic below which the map
`b ↦ ‖b̌ ∈ τ‖` is monotone, preserves intersections, kills the zero of the completion and is
above the top. -/
theorem exists_orbitValue_condition (A : ForcingContext V) {Pf : SetTheorySemisentence 2}
    {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    {τ : V} (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) :
    ∃ p₀ ∈ booleanConditions A.P A.R,
      (∃ q ∈ A.G, q ∈ p₀) ∧
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
        A.booleanMemValue τ b ∩ p₀ ⊆ A.booleanMemValue τ c) ∧
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R,
        A.booleanMemValue τ b ∩ A.booleanMemValue τ c ∩ p₀ ⊆ A.booleanMemValue τ (b ∩ c)) ∧
      A.booleanMemValue τ (∅ : V) ∩ p₀ = ∅ ∧
      p₀ ⊆ A.booleanMemValue τ A.P := by
  classical
  -- the clauses of the filter, read on checked conditions
  have hupward : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
      A.check b ∈ H → A.check c ∈ H := by
    intro b _ c hc hbc hbH
    refine hH.2.1 _ hbH (A.check c) ?_ ((A.checkEmbedding.subset_iff _ _).mpr hbc)
    exact (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hc))
  have hmeet : ∀ b c : V, A.check b ∈ H → A.check c ∈ H → A.check (b ∩ c) ∈ H := by
    intro b c hbH hcH
    rw [A.check_inter]
    exact hH.2.2.1 _ hbH _ hcH
  have hnotEmptyH : A.check (∅ : V) ∉ H := by
    intro hmem
    obtain ⟨z, hz⟩ := hH.2.2.2.1 _ hmem
    rw [A.check_empty] at hz
    exact not_mem_empty hz
  have hmeetsTop : ∃ q ∈ A.G, q ∈ A.booleanMemValue τ A.P := (hval A.P).mp hH.2.2.2.2.2.1
  have hnotMeetsEmpty : ¬ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ (∅ : V) :=
    fun h ↦ hnotEmptyH ((hval ∅).mpr h)
  -- the condition for the top
  obtain ⟨q₅, hq₅G, hq₅⟩ := hmeetsTop
  have hq₅P : q₅ ∈ A.P := A.generic.1.1 q₅ hq₅G
  have hs₅B : coneRegular A.P A.R q₅ ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hq₅P
  have hs₅sub : coneRegular A.P A.R q₅ ⊆ A.booleanMemValue τ A.P :=
    coneRegular_subset_of_mem A.order (A.booleanMemValue_regular τ A.P) hq₅
  have hs₅G : ∃ q ∈ A.G, q ∈ coneRegular A.P A.R q₅ :=
    ⟨q₅, hq₅G, self_mem_coneRegular A.order hq₅P⟩
  -- the condition for the zero
  have hD₄ : ForcingDense A.P A.R
      (A.booleanMemValue τ (∅ : V) ∪ forcingNegation A.P A.R (A.booleanMemValue τ (∅ : V))) := by
    constructor
    · intro z hz
      rcases mem_union_iff.mp hz with h | h
      · exact (A.booleanMemValue_regular τ ∅).1 z h
      · exact forcingNegation_subset _ _ _ z h
    · intro z hz
      by_cases hze : z ∈ A.booleanMemValue τ (∅ : V)
      · exact ⟨z, mem_union_iff.mpr (Or.inl hze), A.order.2.1 z hz⟩
      · obtain ⟨w, hw, hwz⟩ :=
          exists_forcingNegation_of_not_mem hz hze (A.booleanMemValue_regular τ ∅).2.2
        exact ⟨w, mem_union_iff.mpr (Or.inr hw), hwz⟩
  obtain ⟨q₄, hq₄G, hq₄D⟩ := A.generic.2 _ hD₄
  have hq₄P : q₄ ∈ A.P := A.generic.1.1 q₄ hq₄G
  have hq₄n : q₄ ∈ forcingNegation A.P A.R (A.booleanMemValue τ (∅ : V)) := by
    rcases mem_union_iff.mp hq₄D with h | h
    · exact absurd ⟨q₄, hq₄G, h⟩ hnotMeetsEmpty
    · exact h
  have hs₄avoid := coneRegular_avoids (A.booleanMemValue_regular τ ∅) hq₄n
  have hs₄B : coneRegular A.P A.R q₄ ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hq₄P
  have hs₄G : ∃ q ∈ A.G, q ∈ coneRegular A.P A.R q₄ :=
    ⟨q₄, hq₄G, self_mem_coneRegular A.order hq₄P⟩
  -- the condition for monotonicity
  obtain ⟨s₂, hs₂gen, hs₂D⟩ :=
    (booleanGeneric_generic A.order A.generic).2 _ (A.orbitMonoSet_dense τ)
  obtain ⟨hs₂B, hs₂G⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hs₂gen
  have hgood₂ : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
      ∀ r, r ∈ A.booleanMemValue τ b → r ∈ s₂ → r ∈ A.booleanMemValue τ c := by
    rcases ((A.mem_orbitMonoSet_iff τ s₂).mp hs₂D).2 with hgood | hbad
    · exact hgood
    · exfalso
      obtain ⟨b, hb, c, hc, hbc, hsb, hsc⟩ := hbad
      obtain ⟨w, hwG, hws⟩ := id hs₂G
      have hcH := hupward b hb c hc hbc ((hval b).mpr ⟨w, hwG, hsb w hws⟩)
      exact meets_false_of_avoids (booleanConditions_regular hs₂B)
        (A.booleanMemValue_regular τ c) hs₂G ((hval c).mp hcH) hsc
  -- the condition for intersections
  obtain ⟨s₃, hs₃gen, hs₃D⟩ :=
    (booleanGeneric_generic A.order A.generic).2 _ (A.orbitInterSet_dense τ)
  obtain ⟨hs₃B, hs₃G⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hs₃gen
  have hgood₃ : ∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, ∀ d, d = b ∩ c →
      ∀ r, r ∈ A.booleanMemValue τ b → r ∈ A.booleanMemValue τ c → r ∈ s₃ →
        r ∈ A.booleanMemValue τ d := by
    rcases ((A.mem_orbitInterSet_iff τ s₃).mp hs₃D).2 with hgood | hbad
    · exact hgood
    · exfalso
      obtain ⟨b, hb, c, hc, d, rfl, hsb, hsc, hsd⟩ := hbad
      obtain ⟨w, hwG, hws⟩ := id hs₃G
      have hbH := (hval b).mpr ⟨w, hwG, hsb w hws⟩
      have hcH := (hval c).mpr ⟨w, hwG, hsc w hws⟩
      exact meets_false_of_avoids (booleanConditions_regular hs₃B)
        (A.booleanMemValue_regular τ (b ∩ c)) hs₃G ((hval (b ∩ c)).mp (hmeet b c hbH hcH)) hsd
  -- intersect the four conditions inside the generic filter
  have hreg₂ := booleanConditions_regular hs₂B
  have hreg₃ := booleanConditions_regular hs₃B
  have hreg₄ : IsForcingRegular A.P A.R (coneRegular A.P A.R q₄) := coneRegular_regular A.order q₄
  have hreg₅ : IsForcingRegular A.P A.R (coneRegular A.P A.R q₅) := coneRegular_regular A.order q₅
  have hreg₂₃ := forcingRegular_inter hreg₂ hreg₃
  have hreg₂₃₄ := forcingRegular_inter hreg₂₃ hreg₄
  have hregp := forcingRegular_inter hreg₂₃₄ hreg₅
  have hG₂₃ := meets_inter hreg₂ hreg₃ hs₂G hs₃G
  have hG₂₃₄ := meets_inter hreg₂₃ hreg₄ hG₂₃ hs₄G
  have hGp := meets_inter hreg₂₃₄ hreg₅ hG₂₃₄ hs₅G
  obtain ⟨w, hwG, hwp⟩ := hGp
  refine ⟨s₂ ∩ s₃ ∩ coneRegular A.P A.R q₄ ∩ coneRegular A.P A.R q₅,
    (mem_booleanConditions_iff _ _ _).mpr ⟨hregp, w, hwp⟩, ⟨w, hwG, hwp⟩, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc hbc z hz
    have hzb := (mem_inter_iff.mp hz).1
    have hzp := (mem_inter_iff.mp hz).2
    have hz₂ := (mem_inter_iff.mp (mem_inter_iff.mp (mem_inter_iff.mp hzp).1).1).1
    exact hgood₂ b hb c hc hbc z hzb hz₂
  · intro b hb c hc z hz
    have hzbc := (mem_inter_iff.mp hz).1
    have hzp := (mem_inter_iff.mp hz).2
    have hz₃ := (mem_inter_iff.mp (mem_inter_iff.mp (mem_inter_iff.mp hzp).1).1).2
    exact hgood₃ b hb c hc (b ∩ c) rfl z (mem_inter_iff.mp hzbc).1 (mem_inter_iff.mp hzbc).2 hz₃
  · apply mem_ext
    intro z
    constructor
    · intro hz
      exact absurd (mem_inter_iff.mp hz).1
        (hs₄avoid z (mem_inter_iff.mp (mem_inter_iff.mp (mem_inter_iff.mp hz).2).1).2)
    · intro hz
      exact (not_mem_empty hz).elim
  · intro z hz
    exact hs₅sub z (mem_inter_iff.mp hz).2

/-! ### The completeness clause -/

/-- Membership in the join of the Boolean values of a ground set of conditions, unfolded. -/
def OrbitJoinMem (A : ForcingContext V) (τ M z : V) : Prop :=
  z ∈ A.P ∧ ∀ q ∈ A.P, ⟨q, z⟩ₖ ∈ A.R →
    ∃ r ∈ A.P, ⟨r, q⟩ₖ ∈ A.R ∧ ∃ b ∈ M, r ∈ A.booleanMemValue τ b

theorem booleanMemValue_mem_range (A : ForcingContext V) {τ M b : V} (hb : b ∈ M) :
    A.booleanMemValue τ b ∈ range (A.booleanValueFamily τ M) := by
  unfold booleanValueFamily
  rw [range_definableGraph]
  exact (repl_spec _).mpr ⟨b, hb, rfl⟩

theorem regularJoin_booleanValueFamily_regular (A : ForcingContext V) (τ M : V) :
    IsForcingRegular A.P A.R (regularJoin A.P A.R (range (A.booleanValueFamily τ M))) := by
  refine regularJoin_regular A.order (fun X hX ↦ ?_)
  exact ((mem_regularSets_iff _ _ _).mp (A.booleanValueFamily_range_subset τ M X hX)).1

theorem orbitJoinMem_iff (A : ForcingContext V) (τ M z : V) :
    A.OrbitJoinMem τ M z ↔ z ∈ regularJoin A.P A.R (range (A.booleanValueFamily τ M)) := by
  unfold OrbitJoinMem regularJoin
  rw [mem_forcingClosure_iff]
  apply and_congr_right
  intro _
  refine forall_congr' fun q ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ ?_
  constructor
  · rintro ⟨r, _, hrq, b, hb, hrb⟩
    exact ⟨r, mem_sUnion_iff.mpr ⟨A.booleanMemValue τ b, A.booleanMemValue_mem_range hb, hrb⟩, hrq⟩
  · rintro ⟨r, hr, hrq⟩
    obtain ⟨X, hX, hrX⟩ := mem_sUnion_iff.mp hr
    simp only [booleanValueFamily, range_definableGraph, repl_spec] at hX
    obtain ⟨b, hb, rfl⟩ := hX
    exact ⟨r, (A.booleanMemValue_regular τ b).1 r hrX, hrq, b, hb, hrX⟩

/-- The Boolean conditions that either send every ground maximal antichain to a family whose join
is above them, or avoid the join of the values of some ground maximal antichain. -/
noncomputable def orbitJoinSet (A : ForcingContext V) (τ : V) : V :=
  sep (booleanConditions A.P A.R)
    (fun s ↦
      (∀ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ s, A.OrbitJoinMem τ M z) ∨
      (∃ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ s, ¬ A.OrbitJoinMem τ M z))
    (by
      have := A.booleanMemValue_definable τ
      unfold OrbitJoinMem
      definability)

theorem mem_orbitJoinSet_iff (A : ForcingContext V) (τ s : V) :
    s ∈ A.orbitJoinSet τ ↔ s ∈ booleanConditions A.P A.R ∧
      ((∀ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ s, A.OrbitJoinMem τ M z) ∨
      (∃ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ s, ¬ A.OrbitJoinMem τ M z)) :=
  mem_sep_iff

theorem orbitJoinSet_dense (A : ForcingContext V) (τ : V) :
    ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) (A.orbitJoinSet τ) := by
  refine ⟨sep_subset, fun u hu ↦ ?_⟩
  by_cases hgood : ∀ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ u, A.OrbitJoinMem τ M z
  · exact ⟨u, (A.mem_orbitJoinSet_iff τ u).mpr ⟨hu, Or.inl hgood⟩,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  · obtain ⟨M, hM, z, hzu, hz⟩ :
        ∃ M ∈ boolMaximalAntichains A.P A.R, ∃ z, z ∈ u ∧ ¬ A.OrbitJoinMem τ M z := by
      by_contra hcon
      refine hgood (fun M hM z hzu ↦ ?_)
      by_contra hz
      exact hcon ⟨M, hM, z, hzu, hz⟩
    have hureg := booleanConditions_regular hu
    have hzP : z ∈ A.P := hureg.1 z hzu
    have hzJ : z ∉ regularJoin A.P A.R (range (A.booleanValueFamily τ M)) :=
      fun h ↦ hz ((A.orbitJoinMem_iff τ M z).mpr h)
    obtain ⟨q, hqP, hqz, havoid⟩ :=
      exists_cone_avoiding (A.regularJoin_booleanValueFamily_regular τ M) hzP hzJ
    have hqu : q ∈ u := hureg.2.1 z hzu q hqP hqz
    have hcone : coneRegular A.P A.R q ∈ booleanConditions A.P A.R :=
      coneRegular_mem_booleanConditions A.order hqP
    refine ⟨coneRegular A.P A.R q, (A.mem_orbitJoinSet_iff τ _).mpr ⟨hcone,
      Or.inr ⟨M, hM, fun t ht hcon ↦ havoid t ht ((A.orbitJoinMem_iff τ M t).mp hcon)⟩⟩, ?_⟩
    exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
      ⟨hcone, hu, coneRegular_subset_of_mem A.order hureg hqu⟩

/-- The homomorphism condition together with the completeness clause: below `p₀` the map
`b ↦ ‖b̌ ∈ τ‖` also sends every ground maximal antichain of the completion to a family whose
join is above `p₀`. -/
theorem exists_orbitValue_condition_complete (A : ForcingContext V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    {τ : V} (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) :
    ∃ p₀ ∈ booleanConditions A.P A.R,
      (∃ q ∈ A.G, q ∈ p₀) ∧
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R, b ⊆ c →
        A.booleanMemValue τ b ∩ p₀ ⊆ A.booleanMemValue τ c) ∧
      (∀ b ∈ booleanConditions A.P A.R, ∀ c ∈ booleanConditions A.P A.R,
        A.booleanMemValue τ b ∩ A.booleanMemValue τ c ∩ p₀ ⊆ A.booleanMemValue τ (b ∩ c)) ∧
      A.booleanMemValue τ (∅ : V) ∩ p₀ = ∅ ∧
      p₀ ⊆ A.booleanMemValue τ A.P ∧
      ∀ M ∈ boolMaximalAntichains A.P A.R,
        p₀ ⊆ regularJoin A.P A.R (range (A.booleanValueFamily τ M)) := by
  classical
  obtain ⟨p₀, hp₀B, hp₀G, hmono, hinter, hzero, htop⟩ := A.exists_orbitValue_condition hH hval
  obtain ⟨s, hsgen, hsD⟩ :=
    (booleanGeneric_generic A.order A.generic).2 _ (A.orbitJoinSet_dense τ)
  obtain ⟨hsB, hsG⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hsgen
  have hgood : ∀ M ∈ boolMaximalAntichains A.P A.R, ∀ z ∈ s, A.OrbitJoinMem τ M z := by
    rcases ((A.mem_orbitJoinSet_iff τ s).mp hsD).2 with hgood | hbad
    · exact hgood
    · exfalso
      obtain ⟨M, hM, havoid⟩ := hbad
      obtain ⟨a, haM, haH⟩ := hH.2.2.2.2.1 (A.check M) ((A.check_mem_iff _ _).mpr hM)
      obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff _ _).mp haM
      obtain ⟨w, hwG, hwb⟩ := (hval b).mp haH
      refine meets_false_of_avoids (booleanConditions_regular hsB)
        (A.regularJoin_booleanValueFamily_regular τ M) hsG
        ⟨w, hwG, subset_regularJoin A.order (A.booleanMemValue_mem_range hb)
          (A.booleanMemValue_regular τ b) w hwb⟩
        (fun t ht hcon ↦ havoid t ht ((A.orbitJoinMem_iff τ M t).mpr hcon))
  have hregp := booleanConditions_regular hp₀B
  have hregs := booleanConditions_regular hsB
  obtain ⟨w, hwG, hwp⟩ := meets_inter hregp hregs hp₀G hsG
  refine ⟨p₀ ∩ s, (mem_booleanConditions_iff _ _ _).mpr
    ⟨forcingRegular_inter hregp hregs, w, hwp⟩, ⟨w, hwG, hwp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc hbc y hy
    exact hmono b hb c hc hbc y (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hy).1, (mem_inter_iff.mp (mem_inter_iff.mp hy).2).1⟩)
  · intro b hb c hc y hy
    exact hinter b hb c hc y (mem_inter_iff.mpr
      ⟨(mem_inter_iff.mp hy).1, (mem_inter_iff.mp (mem_inter_iff.mp hy).2).1⟩)
  · apply mem_ext
    intro y
    constructor
    · intro hy
      have : y ∈ A.booleanMemValue τ (∅ : V) ∩ p₀ := mem_inter_iff.mpr
        ⟨(mem_inter_iff.mp hy).1, (mem_inter_iff.mp (mem_inter_iff.mp hy).2).1⟩
      rwa [hzero] at this
    · intro hy
      exact (not_mem_empty hy).elim
  · intro y hy
    exact htop y (mem_inter_iff.mp hy).1
  · intro M hM y hy
    exact (A.orbitJoinMem_iff τ M y).mp (hgood M hM y (mem_inter_iff.mp hy).2)


end ForcingContext

end ZFVP
