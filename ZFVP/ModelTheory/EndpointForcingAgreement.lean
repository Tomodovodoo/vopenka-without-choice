import ZFVP.ModelTheory.EndpointForcingAbsoluteness
import ZFVP.ModelTheory.ForcingWindowTransfer

/-! # The two halves of the endpoint forcing agreement

The paper's displayed equation inside the finite window lemma says that a condition of the
small poset forces a formula of a fixed Levy level exactly when its image forces the same
formula over the big poset, and that the same holds for the negation.  This file splits that
statement into the part that is absoluteness and the part that is a genuine forcing fact.

* `endpointForcing_rank_agreement` is the absoluteness half.  The defining formula of the
  forcing relation at level `(pol, k)` computes the same relation inside any rank stage that
  is `Cn (uniformForcingLevelBound pol k)` and contains the arguments, and that relation is
  the true one of `V`.  Two such stages therefore agree with each other.  This is what makes
  the numeral `uniformForcingLevelBound pol k` an effective bound: one numeral works at both
  ends of the window.

* `endpointForcing_negation_agreement` is the negation clause.  It is derived from agreement
  of the forcing sets along the section, and it needs one further hypothesis,
  `IsDenseForcingSection`, which is discussed at that theorem.

* `endpointForcing_levelAgreement` assembles `ForcingLevelAgreement` from a single named
  hypothesis `hforces`, the complete-embedding preservation of the forcing relation, plus the
  negation clause proved here.

Everything is parametric in the posets `P0 R0 P1 R1`, the projection `π`, the section `E` and
the name sets `D0 D1`.  No forcing iteration and no endpoint set occurs; the word endpoint is
only in the names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The absoluteness half -/

theorem cn_isOrdinal {k : ℕ} {ξ : V} (h : Cn k ξ) : IsOrdinal ξ := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- A correct stage below another correct stage has a smaller rank hierarchy.  This is how a
caller turns `ξ ⊆ ζ` into the subset hypothesis of `endpointForcing_rank_agreement`. -/
theorem hierarchy_subset_of_cn {k l : ℕ} {ξ ζ : V} (hξ : Cn k ξ) (hζ : Cn l ζ) (h : ξ ⊆ ζ) :
    hierarchy ξ ⊆ hierarchy ζ := by
  have : IsOrdinal ξ := cn_isOrdinal hξ
  have : IsOrdinal ζ := cn_isOrdinal hζ
  exact hierarchy_mono h

/-- The absoluteness half of the endpoint agreement.  Let `ξ` and `ζ` be two rank stages that
are correct at the exact Levy bound of the level formula, with `hierarchy ξ ⊆ hierarchy ζ`,
and let all seven arguments lie in the smaller one.  Then the forcing relation computed inside
`hierarchy ξ`, the one computed inside `hierarchy ζ`, and the true one of `V` all coincide.

The first conjunct is the agreement of the two stages, the second identifies both with the
forcing set of `V`.  Nothing here is a hypothesis about the posets: only `b ∈ D ^ n` and
`q ∈ P`, which the defining formula needs in order to mean anything. -/
theorem endpointForcing_rank_agreement {pol : LevyPolarity} {k : ℕ} {ξ ζ P R D n φ b q : V}
    (hξ : Cn (uniformForcingLevelBound pol k) ξ)
    (hζ : Cn (uniformForcingLevelBound pol k) ζ)
    (hsub : hierarchy ξ ⊆ hierarchy ζ)
    (hb : b ∈ D ^ n) (hq : q ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hq' : q ∈ hierarchy ξ) :
    ((uniformForcingLevelFormula pol k).Evalb
        (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
          Fin 7 → SetDomain (hierarchy ξ)) ↔
      (uniformForcingLevelFormula pol k).Evalb
        (![⟨P, hsub P hP⟩, ⟨R, hsub R hR⟩, ⟨D, hsub D hD⟩, ⟨n, hsub n hn⟩, ⟨φ, hsub φ hφ⟩,
            ⟨b, hsub b hb'⟩, ⟨q, hsub q hq'⟩] : Fin 7 → SetDomain (hierarchy ζ))) ∧
    ((uniformForcingLevelFormula pol k).Evalb
        (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
          Fin 7 → SetDomain (hierarchy ξ)) ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b) := by
  have h0 := uniformForcingLevel_absolute hξ hb hq hP hR hD hn hφ hb' hq'
  have h1 := uniformForcingLevel_absolute hζ hb hq (hsub P hP) (hsub R hR) (hsub D hD)
    (hsub n hn) (hsub φ hφ) (hsub b hb') (hsub q hq')
  exact ⟨h0.trans h1.symm, h0⟩

/-- The same statement for the Pi companion of the level formula, so that the agreement holds
for both readings of the Delta one definition. -/
theorem endpointForcing_rank_agreement_pi {pol : LevyPolarity} {k : ℕ} {ξ ζ P R D n φ b q : V}
    (hξ : Cn (uniformForcingLevelBound pol k) ξ)
    (hζ : Cn (uniformForcingLevelBound pol k) ζ)
    (hsub : hierarchy ξ ⊆ hierarchy ζ)
    (hb : b ∈ D ^ n) (hq : q ∈ P)
    (hP : P ∈ hierarchy ξ) (hR : R ∈ hierarchy ξ) (hD : D ∈ hierarchy ξ)
    (hn : n ∈ hierarchy ξ) (hφ : φ ∈ hierarchy ξ) (hb' : b ∈ hierarchy ξ)
    (hq' : q ∈ hierarchy ξ) :
    ((uniformForcingLevelPiFormula pol k).Evalb
        (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
          Fin 7 → SetDomain (hierarchy ξ)) ↔
      (uniformForcingLevelPiFormula pol k).Evalb
        (![⟨P, hsub P hP⟩, ⟨R, hsub R hR⟩, ⟨D, hsub D hD⟩, ⟨n, hsub n hn⟩, ⟨φ, hsub φ hφ⟩,
            ⟨b, hsub b hb'⟩, ⟨q, hsub q hq'⟩] : Fin 7 → SetDomain (hierarchy ζ))) ∧
    ((uniformForcingLevelPiFormula pol k).Evalb
        (![⟨P, hP⟩, ⟨R, hR⟩, ⟨D, hD⟩, ⟨n, hn⟩, ⟨φ, hφ⟩, ⟨b, hb'⟩, ⟨q, hq'⟩] :
          Fin 7 → SetDomain (hierarchy ξ)) ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b) := by
  have h0 := uniformForcingLevelPi_absolute hξ hb hq hP hR hD hn hφ hb' hq'
  have h1 := uniformForcingLevelPi_absolute hζ hb hq (hsub P hP) (hsub R hR) (hsub D hD)
    (hsub n hn) (hsub φ hφ) (hsub b hb') (hsub q hq')
  exact ⟨h0.trans h1.symm, h0⟩

/-! ### The negation clause -/

/-- The image of the section is dense below the image of every small condition: every big
condition below `E ‘ q` has a small condition below `q` whose section lies below it.

This is the extra hypothesis the negation clause needs.  Without it the clause is false.  Take
`P0 = {1}` with the trivial order, `P1 = {1, a, b}` with `a` and `b` incompatible below `1`,
`π` constant and `E ‘ 1 = 1`.  Then `A1 = {a}` is downward closed and even regular, and the
only value of `hagree` forces `A0 = ∅`.  Now `1 ∈ forcingNegation P0 R0 A0` while
`E ‘ 1 = 1 ∉ forcingNegation P1 R1 A1`, because `a ≤ 1` lies in `A1`.  So agreement of the two
sets along the section, downward closure and even a split projection do not by themselves give
agreement of the negations. -/
def IsDenseForcingSection (P0 R0 P1 R1 E : V) : Prop :=
  ∀ q ∈ P0, ∀ s ∈ P1, ⟨s, E ‘ q⟩ₖ ∈ R1 → ∃ r ∈ P0, ⟨r, q⟩ₖ ∈ R0 ∧ ⟨E ‘ r, s⟩ₖ ∈ R1

/-- Agreement of two sets along the section transfers to their forcing negations, provided the
section image is dense below every `E ‘ q` and the big set is downward closed.

The easy direction only uses monotonicity of the section: a small condition below `q` inside
`A0` has its section below `E ‘ q` inside `A1`.  The other direction is the one that needs
density: a big condition below `E ‘ q` inside `A1` is refined by the section of a small
condition below `q`, and downward closure puts that section into `A1`. -/
theorem endpointForcing_negation_agreement {P0 R0 P1 R1 π E A0 A1 : V}
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E)
    (hdense : IsDenseForcingSection P0 R0 P1 R1 E)
    (hA1 : IsForcingDownwardClosed P1 R1 A1)
    (hagree : ∀ q ∈ P0, q ∈ A0 ↔ E ‘ q ∈ A1) :
    ∀ q ∈ P0, q ∈ forcingNegation P0 R0 A0 ↔ E ‘ q ∈ forcingNegation P1 R1 A1 := by
  intro q hq
  rw [mem_forcingNegation_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨-, hno⟩
    refine ⟨function_value_mem hsplit.maps hq, ?_⟩
    intro s hs hsq hsA
    obtain ⟨r, hr, hrq, hrs⟩ := hdense q hq s hs hsq
    exact hno r hr hrq ((hagree r hr).mpr
      (hA1 s hsA (E ‘ r) (function_value_mem hsplit.maps hr) hrs))
  · rintro ⟨-, hno⟩
    refine ⟨hq, ?_⟩
    intro r hr hrq hrA
    exact hno (E ‘ r) (function_value_mem hsplit.maps hr) (hsplit.monotone hr hq hrq)
      ((hagree r hr).mp hrA)

/-! ### The assembled level agreement -/

/-- The paper's endpoint forcing agreement at level `(pol, k)`, assembled from one owed fact.

`hforces` is the complete-embedding half: a small condition forces a code of level `(pol, k)`
exactly when its section forces the same code over the big poset.  It is not proved here.  The
negation clause is proved from it by `endpointForcing_negation_agreement`, so the integrator
owes one fact rather than two. -/
theorem endpointForcing_levelAgreement {P0 R0 P1 R1 π E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hR1 : IsForcingPreorder P1 R1)
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E)
    (hdense : IsDenseForcingSection P0 R0 P1 R1 E)
    (hD : D0 ⊆ D1)
    (hforces : ∀ n φ, IsLevyFormulaCode pol k n φ → ∀ b ∈ D0 ^ n, ∀ q ∈ P0,
      q ∈ internalForcingSet P0 R0 D0 n φ b ↔ E ‘ q ∈ internalForcingSet P1 R1 D1 n φ b) :
    ForcingLevelAgreement P0 R0 P1 R1 E D0 D1 pol k := by
  refine ⟨hforces, ?_⟩
  intro n φ hφ b hb
  have hb1 : b ∈ D1 ^ n := mem_function_of_mem_function_of_subset hb hD
  have hdown : IsForcingDownwardClosed P1 R1 (internalForcingSet P1 R1 D1 n φ b) :=
    (internalForcingSet_regular hR1 hφ.membershipCode hb1).2.1
  exact endpointForcing_negation_agreement hsplit hdense hdown (hforces n φ hφ b hb)

end ZFVP
