import ZFVP.Syntax.BoundedNegation
import ZFVP.SetTheory.ForcingNegationCalculus
import ZFVP.ModelTheory.ForcingWindowTransfer

/-!
# The forcing negation clause for internal formula codes

The paper's finite window lemma transfers the agreement of the two forcing relations from a
formula to its negation with one sentence, appealing to the closure of the code family under
negation. This file supplies that step.

* `internalForcingSet_negate` says that the set of conditions forcing the negation normal
  form dual `negateFormula` of a code is the forcing negation of the set of conditions
  forcing the code. It is proved by induction over the eight constructors.
* `IsLevyFormulaCode.negate` says that the Levy code family is closed under that dual, at the
  same level `k` with the polarity flipped. The bounded case is `IsBoundedFormulaCode.neg`.
* `forcingLevelAgreement_of_forces` builds a `ForcingLevelAgreement` from agreement of the
  forcing relations alone. Because the negated code is again a code of level `k` (at the dual
  polarity) and its forcing set is the forcing negation, the `refutes` field is the `forces`
  hypothesis at the dual polarity. This route removes the need for the extra hypothesis
  `IsDenseForcingSection` used by `endpointForcing_levelAgreement`, so an integrator should
  prefer it.

Everything is parametric in the posets and the name sets. No forcing iteration and no
endpoint occurs.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two set-level De Morgan laws -/

/-- The negation of a regular join of two regular sets is the intersection of the negations.
This is the shape of the join produced by the `or` clause of the internal forcing relation. -/
theorem forcingNegation_forcingClosure_union {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B) :
    forcingNegation P R (forcingClosure P R (A ∪ B)) =
      forcingNegation P R A ∩ forcingNegation P R B := by
  apply mem_ext
  intro p
  rw [mem_inter_iff, mem_forcingNegation_iff, mem_forcingNegation_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨hp, hno⟩
    refine ⟨⟨hp, ?_⟩, ⟨hp, ?_⟩⟩
    · intro q hq hqp hqA
      exact hno q hq hqp ((mem_forcingClosure_iff _ _ _ _).mpr ⟨hq, fun s hs hsq ↦
        ⟨s, mem_union_iff.mpr (Or.inl (hA.2.1 q hqA s hs hsq)), hR.2.1 s hs⟩⟩)
    · intro q hq hqp hqB
      exact hno q hq hqp ((mem_forcingClosure_iff _ _ _ _).mpr ⟨hq, fun s hs hsq ↦
        ⟨s, mem_union_iff.mpr (Or.inr (hB.2.1 q hqB s hs hsq)), hR.2.1 s hs⟩⟩)
  · rintro ⟨⟨hp, hnoA⟩, ⟨-, hnoB⟩⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp hqC
    obtain ⟨-, hh⟩ := (mem_forcingClosure_iff _ _ _ _).mp hqC
    obtain ⟨r, hr, hrq⟩ := hh q hq (hR.2.1 q hq)
    have hrP : r ∈ P := (mem_union_iff.mp hr).elim (hA.1 r) (hB.1 r)
    have hrp : (⟨r, p⟩ₖ : V) ∈ R := hR.2.2 r hrP q hq p hp hrq hqp
    exact (mem_union_iff.mp hr).elim (hnoA r hrP hrp) (hnoB r hrP hrp)

/-- The negation of an intersection of two regular sets, written with the closure of the union
that the `or` clause of the internal forcing relation produces. -/
theorem forcingNegation_inter_eq_closure {P R A B : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B) :
    forcingNegation P R (A ∩ B) =
      forcingClosure P R (forcingNegation P R A ∪ forcingNegation P R B) := by
  rw [forcingNegation_inter hR hA hB, regularJoin, sUnion_pair_eq]

/-! ### Closure of the Levy code family under the dual -/

/-- The Levy code family of level `k` is closed under the negation normal form dual, with the
polarity flipped and the level unchanged. -/
theorem IsLevyFormulaCode.negate {p : LevyPolarity} {k : ℕ} {n φ : V}
    (hφ : IsLevyFormulaCode p k n φ) :
    IsLevyFormulaCode p.dual k n (negateFormula membershipLanguageCode ∅ n φ) := by
  induction k generalizing p n φ with
  | zero => exact IsBoundedFormulaCode.neg hφ
  | succ k ih =>
    revert hφ
    refine levyFormulaCode_successor_induction k p (fun n φ ↦
      IsLevyFormulaCode p.dual (k + 1) n (negateFormula membershipLanguageCode ∅ n φ))
      (by definability) ?_ ?_ ?_ ?_ n φ
    · intro q n φ hq
      exact (ih hq).raise
    · intro n hn φ ψ hφ hψ ihφ ihψ
      rw [negateFormula_and membershipLanguageCode_valid hn hφ.valid hψ.valid,
        negateFormula_or membershipLanguageCode_valid hn hφ.valid hψ.valid]
      exact ⟨ihφ.or ihψ, ihφ.and ihψ⟩
    · intro n hn i hi φ hφ ih2
      rw [negateFormula_boundedAll hn hi hφ.valid, negateFormula_boundedExists hn hi hφ.valid]
      exact ⟨IsLevyFormulaCode.boundedExists hn hi ih2, IsLevyFormulaCode.boundedAll hn hi ih2⟩
    · intro n hn φ hφ ih2
      cases p with
      | sigma =>
        show IsLevyFormulaCode _ _ n (negateFormula membershipLanguageCode ∅ n (existsCode φ))
        rw [negateFormula_exists membershipLanguageCode_valid hn hφ.valid]
        exact IsLevyFormulaCode.quantifier (p := .pi) hn ih2
      | pi =>
        show IsLevyFormulaCode _ _ n (negateFormula membershipLanguageCode ∅ n (allCode φ))
        rw [negateFormula_all membershipLanguageCode_valid hn hφ.valid]
        exact IsLevyFormulaCode.quantifier (p := .sigma) hn ih2

/-! ### The forcing negation clause -/

/-- The conditions forcing the dual of a code are exactly the forcing negation of the
conditions forcing the code. The proof is an induction over the eight constructors: the atomic
cases are the two atomic clauses and the double negation law for regular sets, the Boolean
cases are the two De Morgan laws above, and the quantifier cases use the regularity of the
forcing sets of the matrix. -/
theorem internalForcingSet_negate {P R D n φ b : V} (hR : IsForcingPreorder P R)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (negateFormula membershipLanguageCode ∅ n φ) b =
      forcingNegation P R (internalForcingSet P R D n φ b) := by
  classical
  have hall : ∀ n : V, ∀ φ ∈ formulaSet (membershipLanguageCode : V) ∅ n, ∀ b ∈ D ^ n,
      internalForcingSet P R D n (negateFormula membershipLanguageCode ∅ n φ) b =
        forcingNegation P R (internalForcingSet P R D n φ b) := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ b ∈ D ^ n,
        internalForcingSet P R D n (negateFormula membershipLanguageCode ∅ n φ) b =
          forcingNegation P R (internalForcingSet P R D n φ b))
      (by definability) ?_ ?_ ?_ ?_
    · intro n hn
      constructor <;> intro b hb
      · rw [negateFormula_truth membershipLanguageCode_valid hn,
          internalForcingSet_falsity (P := P) (R := R) (D := D) (b := b) hn,
          internalForcingSet_truth (P := P) (R := R) hn hb, forcingNegation_top hR]
      · rw [negateFormula_falsity membershipLanguageCode_valid hn,
          internalForcingSet_truth (P := P) (R := R) hn hb,
          internalForcingSet_falsity (P := P) (R := R) (D := D) (b := b) hn,
          forcingNegation_empty]
    · intro n hn r args ha
      constructor <;> intro b hb
      · rw [negateFormula_atom membershipLanguageCode_valid hn ha,
          internalForcingSet_negAtom hn ha hb, internalForcingSet_atom hn ha hb]
      · rw [negateFormula_negAtom membershipLanguageCode_valid hn ha,
          internalForcingSet_atom hn ha hb, internalForcingSet_negAtom hn ha hb,
          forcingNegation_negation hR
            (internalAtomicForcingSet_regular hR ((membershipAtomicArguments_iff hn).mp ha))]
    · intro n hn φ ψ hφ hψ ihφ ihψ
      have hφc : IsMembershipFormulaCode n φ := (mem_formulaSet_iff _ _ _ _).mp hφ
      have hψc : IsMembershipFormulaCode n ψ := (mem_formulaSet_iff _ _ _ _).mp hψ
      have hnφ : IsMembershipFormulaCode n (negateFormula membershipLanguageCode ∅ n φ) :=
        (mem_formulaSet_iff _ _ _ _).mp (negateFormula_mem membershipLanguageCode_valid hφ)
      have hnψ : IsMembershipFormulaCode n (negateFormula membershipLanguageCode ∅ n ψ) :=
        (mem_formulaSet_iff _ _ _ _).mp (negateFormula_mem membershipLanguageCode_valid hψ)
      constructor <;> intro b hb
      · rw [negateFormula_and membershipLanguageCode_valid hn hφ hψ,
          internalForcingSet_or hnφ hnψ hb, internalForcingSet_and hφc hψc hb,
          ihφ b hb, ihψ b hb, forcingNegation_inter_eq_closure hR
            (internalForcingSet_regular hR hφc hb) (internalForcingSet_regular hR hψc hb)]
      · rw [negateFormula_or membershipLanguageCode_valid hn hφ hψ,
          internalForcingSet_and hnφ hnψ hb, internalForcingSet_or hφc hψc hb,
          ihφ b hb, ihψ b hb, forcingNegation_forcingClosure_union hR
            (internalForcingSet_regular hR hφc hb) (internalForcingSet_regular hR hψc hb)]
    · intro n hn φ hφ ih
      have hφc : IsMembershipFormulaCode (succ n) φ := (mem_formulaSet_iff _ _ _ _).mp hφ
      have hnφ : IsMembershipFormulaCode (succ n)
          (negateFormula membershipLanguageCode ∅ (succ n) φ) :=
        (mem_formulaSet_iff _ _ _ _).mp (negateFormula_mem membershipLanguageCode_valid hφ)
      constructor <;> intro b hb
      · -- the universal code: its dual is an existential code
        have hreg : ∀ x ∈ D, IsForcingRegular P R
            (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) :=
          fun x hx ↦ internalForcingSet_regular hR hφc (assignmentPrepend_mem_function hn hb hx)
        have hneg : ∀ x ∈ D, ∀ t : V,
            (InternalForces P R D (succ n) (negateFormula membershipLanguageCode ∅ (succ n) φ)
              (assignmentPrepend n b x) t ↔ t ∈ forcingNegation P R
                (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x))) := by
          intro x hx t
          rw [← ih (assignmentPrepend n b x) (assignmentPrepend_mem_function hn hb hx),
            mem_internalForcingSet hnφ]
        rw [negateFormula_all membershipLanguageCode_valid hn hφ]
        apply mem_ext
        intro p
        rw [mem_internalForcingSet_raw, mem_forcingNegation_iff]
        refine and_congr_right fun hp ↦ ?_
        rw [internalForces_exists hn hnφ.valid hb hp]
        constructor
        · intro h q hq hqp hqmem
          obtain ⟨hqP, hqf⟩ := (mem_internalForcingSet_raw _ _ _ _ _ _ _).mp hqmem
          rw [internalForces_all hn hφc.valid hb hqP] at hqf
          obtain ⟨r, hrP, hrq, x, hx, hforce⟩ := h q hq hqp
          have hrn := (hneg x hx r).mp hforce
          exact forcingNegation_disjoint hR hrn
            ((hreg x hx).2.1 q ((mem_internalForcingSet hφc).mpr (hqf x hx)) r hrP hrq)
        · intro h q hq hqp
          have hnot : ¬ ∀ x ∈ D,
              InternalForces P R D (succ n) φ (assignmentPrepend n b x) q := by
            intro hc
            exact h q hq hqp ((mem_internalForcingSet_raw _ _ _ _ _ _ _).mpr
              ⟨hq, (internalForces_all hn hφc.valid hb hq).mpr hc⟩)
          push_neg at hnot
          obtain ⟨x, hx, hxn⟩ := hnot
          have hqx : q ∉ internalForcingSet P R D (succ n) φ (assignmentPrepend n b x) :=
            fun hc ↦ hxn ((mem_internalForcingSet hφc).mp hc)
          obtain ⟨r, hrn, hrq⟩ := exists_forcingNegation_of_not_mem hq hqx (hreg x hx).2.2
          exact ⟨r, forcingNegation_subset _ _ _ r hrn, hrq, x, hx, (hneg x hx r).mpr hrn⟩
      · -- the existential code: its dual is a universal code
        have hreg : ∀ x ∈ D, IsForcingRegular P R
            (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) :=
          fun x hx ↦ internalForcingSet_regular hR hφc (assignmentPrepend_mem_function hn hb hx)
        have hneg : ∀ x ∈ D, ∀ t : V,
            (InternalForces P R D (succ n) (negateFormula membershipLanguageCode ∅ (succ n) φ)
              (assignmentPrepend n b x) t ↔ t ∈ forcingNegation P R
                (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x))) := by
          intro x hx t
          rw [← ih (assignmentPrepend n b x) (assignmentPrepend_mem_function hn hb hx),
            mem_internalForcingSet hnφ]
        rw [negateFormula_exists membershipLanguageCode_valid hn hφ]
        apply mem_ext
        intro p
        rw [mem_internalForcingSet_raw, mem_forcingNegation_iff]
        refine and_congr_right fun hp ↦ ?_
        rw [internalForces_all hn hnφ.valid hb hp]
        constructor
        · intro h q hq hqp hqmem
          obtain ⟨hqP, hqf⟩ := (mem_internalForcingSet_raw _ _ _ _ _ _ _).mp hqmem
          rw [internalForces_exists hn hφc.valid hb hqP] at hqf
          obtain ⟨r, hrP, hrq, x, hx, hforce⟩ := hqf q hq (hR.2.1 q hq)
          obtain ⟨-, hno⟩ := (mem_forcingNegation_iff _ _ _ _).mp ((hneg x hx p).mp (h x hx))
          exact hno r hrP (hR.2.2 r hrP q hq p hp hrq hqp)
            ((mem_internalForcingSet hφc).mpr hforce)
        · intro h x hx
          refine (hneg x hx p).mpr ((mem_forcingNegation_iff _ _ _ _).mpr ⟨hp, ?_⟩)
          intro q hq hqp hqx
          refine h q hq hqp ((mem_internalForcingSet_raw _ _ _ _ _ _ _).mpr
            ⟨hq, (internalForces_exists hn hφc.valid hb hq).mpr ?_⟩)
          intro s hs hsq
          exact ⟨s, hs, hR.2.1 s hs, x, hx, (mem_internalForcingSet hφc).mp
            ((hreg x hx).2.1 q hqx s hs hsq)⟩
  exact hall n φ hφ.valid b hb

/-! ### The level agreement with no density hypothesis -/

/-- The paper's endpoint forcing agreement at level `(pol, k)`, assembled from agreement of
the forcing relations alone.

`hforces` is quantified over both polarities, which is the honest reading of the paper's
appeal to closure of the code family under negation: the code family whose forcing relations
agree has to contain the negation of every code it contains. The `refutes` field is then
`hforces` at the dual polarity, applied to the negated code and rewritten by
`internalForcingSet_negate` on both sides.

This drops the extra hypothesis `IsDenseForcingSection` that
`endpointForcing_levelAgreement` needs, so this is the route an integrator should prefer. -/
theorem forcingLevelAgreement_of_forces {P0 R0 P1 R1 E D0 D1 : V} {pol : LevyPolarity} {k : ℕ}
    (hR0 : IsForcingPreorder P0 R0) (hR1 : IsForcingPreorder P1 R1)
    (hD : D0 ⊆ D1)
    (hforces : ∀ (p : LevyPolarity) n φ, IsLevyFormulaCode p k n φ → ∀ b ∈ D0 ^ n, ∀ q ∈ P0,
      q ∈ internalForcingSet P0 R0 D0 n φ b ↔ E ‘ q ∈ internalForcingSet P1 R1 D1 n φ b) :
    ForcingLevelAgreement P0 R0 P1 R1 E D0 D1 pol k := by
  refine ⟨hforces pol, ?_⟩
  intro n φ hφ b hb q hq
  have hb1 : b ∈ D1 ^ n := mem_function_of_mem_function_of_subset hb hD
  rw [← internalForcingSet_negate hR0 hφ.membershipCode hb,
    ← internalForcingSet_negate hR1 hφ.membershipCode hb1]
  exact hforces pol.dual n _ hφ.negate b hb q hq

end ZFVP
