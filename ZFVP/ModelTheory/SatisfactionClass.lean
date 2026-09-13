import ZFVP.Syntax.InternalAtomicForcingRegular
import ZFVP.Syntax.MembershipTruthTables
import ZFVP.Syntax.MembershipSatisfaction
import ZFVP.Syntax.SetDiagonalization
import ZFVP.ModelTheory.NaturalSyntaxStandard

/-! Full satisfaction classes (Enayat, Definition 2.7).

A full satisfaction class for a model of ZF is a predicate on the internally coded formulas of the
membership language, with arbitrary set assignments, obeying the Tarski clauses with the quantifiers
ranging over the whole model. This is the same list of clauses as `MembershipTruthClauses`, except
that there is no ambient set bounding the quantifiers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `S n φ b` reads "the coded formula `φ` with `n` free variables holds under the assignment `b`".
The clauses are those of `MembershipTruthClauses` with the two quantifier cases ranging over all of
`V` instead of over the elements of a set. -/
def IsFullSatisfactionClass (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (S : V → V → V → Prop) : Prop :=
  ∀ n ∈ (ω : V), ∀ b : V, IsFunction b → domain b = n →
    (S n truthCode b ∧ ¬ S n falsityCode b) ∧
    (∀ r args, IsMembershipAtomicArguments n r args →
      (S n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args) ∧
      (S n (negAtomCode r args) b ↔ ¬ DirectMembershipAtomicHolds n b r args)) ∧
    (∀ φ ψ, IsMembershipFormulaCode n φ → IsMembershipFormulaCode n ψ →
      (S n (andCode φ ψ) b ↔ S n φ b ∧ S n ψ b) ∧
      (S n (orCode φ ψ) b ↔ S n φ b ∨ S n ψ b)) ∧
    ∀ φ, IsMembershipFormulaCode (succ n) φ →
      (S n (allCode φ) b ↔ ∀ x : V, S (succ n) φ (assignmentPrepend n b x)) ∧
      (S n (existsCode φ) b ↔ ∃ x : V, S (succ n) φ (assignmentPrepend n b x))

/-- Every term of the membership language is a bound variable. -/
theorem setSemiterm_eq_bvar {n : ℕ} (t : SetTheorySemiterm Empty n) : ∃ i : Fin n, t = .bvar i := by
  cases t with
  | bvar i => exact ⟨i, rfl⟩
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

/-- The argument vector of an atom of the membership language is a vector of bound variables. -/
theorem setSemiterms_eq_bvars {n k : ℕ} (ts : Fin k → SetTheorySemiterm Empty n) :
    ∃ f : Fin k → Fin n, ts = fun i ↦ .bvar (f i) :=
  ⟨fun i ↦ (setSemiterm_eq_bvar (ts i)).choose,
    funext fun i ↦ (setSemiterm_eq_bvar (ts i)).choose_spec⟩

/-- Atomic truth for an equality atom over a pair of bound variables. -/
theorem directMembershipAtomicHolds_eq {n i j B : V} (hi : i ∈ n) (hj : j ∈ n) :
    DirectMembershipAtomicHolds n B (relationToken (0 : V)) (boundPairArguments i j) ↔
      B ‘ i = B ‘ j := by
  constructor
  · rintro ⟨i', hi', j', hj', hargs, h⟩
    obtain ⟨rfl, rfl⟩ := boundPairArguments_inj.mp hargs.symm
    rcases h with ⟨_, he⟩ | ⟨hr, _⟩
    · exact he
    · exact absurd ((relationToken_inj _ _).mp hr) zero_ne_one
  · intro h
    exact ⟨i, hi, j, hj, rfl, Or.inl ⟨Or.inr rfl, h⟩⟩

/-- Atomic truth for a membership atom over a pair of bound variables. -/
theorem directMembershipAtomicHolds_mem {n i j B : V} (hi : i ∈ n) (hj : j ∈ n) :
    DirectMembershipAtomicHolds n B (relationToken (1 : V)) (boundPairArguments i j) ↔
      B ‘ i ∈ B ‘ j := by
  constructor
  · rintro ⟨i', hi', j', hj', hargs, h⟩
    obtain ⟨rfl, rfl⟩ := boundPairArguments_inj.mp hargs.symm
    rcases h with ⟨hr, _⟩ | ⟨_, hm⟩
    · rcases hr with hr | hr
      · exact absurd hr.symm (equalityToken_ne_relationToken _)
      · exact absurd ((relationToken_inj _ _).mp hr).symm zero_ne_one
    · exact hm
  · intro h
    exact ⟨i, hi, j, hj, rfl, Or.inr ⟨rfl, h⟩⟩

theorem isMembershipFormulaCode_encode {n : ℕ} (φ : SetTheorySemisentence n) :
    IsMembershipFormulaCode (n : V) (encodeMembershipFormula φ) :=
  (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem φ)

theorem standardTuple_cons {n : ℕ} (x : V) (b : Fin n → V) :
    standardTuple (x :> b) = assignmentPrepend (n : V) (standardTuple b) x := by
  simp [standardTuple]

theorem membershipAtomicArguments_pair {n : ℕ} (i j : Fin n) {t : V} (ht : t = 0 ∨ t = 1) :
    IsMembershipAtomicArguments (V := V) (n : V) (relationToken t)
      (boundPairArguments (i.val : V) (j.val : V)) := by
  refine ⟨?_, (i.val : V), natCast_mem_of_lt i.isLt, (j.val : V), natCast_mem_of_lt j.isLt, rfl⟩
  rcases ht with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem standardTuple_boundVarCode {n : ℕ} (f : Fin 2 → Fin n) :
    standardTuple (fun k ↦ boundVarCode ((f k).val : V)) =
      boundPairArguments ((f 0).val : V) ((f 1).val : V) := by
  unfold boundPairArguments
  congr 1
  funext k
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) k <;> rfl

theorem encodeMembershipFormula_rel_bvar {n : ℕ} (r : Language.Set.Rel 2) (f : Fin 2 → Fin n)
    {t : V} (ht : membershipSymbol r = t) :
    encodeMembershipFormula (V := V) (.rel r (fun k ↦ .bvar (f k))) =
      atomCode (relationToken t) (boundPairArguments ((f 0).val : V) ((f 1).val : V)) := by
  subst ht
  have h : encodeMembershipFormula (V := V) (.rel r (fun k ↦ .bvar (f k))) =
      atomCode (relationToken (membershipSymbol r))
        (standardTuple (fun k ↦ boundVarCode ((f k).val : V))) := rfl
  rw [h, standardTuple_boundVarCode]

theorem encodeMembershipFormula_nrel_bvar {n : ℕ} (r : Language.Set.Rel 2) (f : Fin 2 → Fin n)
    {t : V} (ht : membershipSymbol r = t) :
    encodeMembershipFormula (V := V) (.nrel r (fun k ↦ .bvar (f k))) =
      negAtomCode (relationToken t) (boundPairArguments ((f 0).val : V) ((f 1).val : V)) := by
  subst ht
  have h : encodeMembershipFormula (V := V) (.nrel r (fun k ↦ .bvar (f k))) =
      negAtomCode (relationToken (membershipSymbol r))
        (standardTuple (fun k ↦ boundVarCode ((f k).val : V))) := rfl
  rw [h, standardTuple_boundVarCode]

/-- On the standard formula codes a full satisfaction class agrees with the model's own
satisfaction relation. -/
theorem IsFullSatisfactionClass.evalb_iff {S : V → V → V → Prop}
    (hS : IsFullSatisfactionClass V S) {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → V) :
    S (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  have key : ∀ {m : ℕ} (ψ : SetTheorySemisentence m) (c : Fin m → V),
      S (m : V) (encodeMembershipFormula ψ) (standardTuple c) ↔ ψ.Evalb c := by
    intro m₀ ψ
    induction ψ with
    | @verum m =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      exact iff_of_true h.1.1 True.intro
    | @falsum m =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      exact iff_of_false h.1.2 (fun x ↦ x)
    | @rel m k r ts =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      cases r
      · obtain ⟨f, rfl⟩ := setSemiterms_eq_bvars ts
        rw [encodeMembershipFormula_rel_bvar _ f (t := (0 : V)) rfl,
          (h.2.1 _ _ (membershipAtomicArguments_pair (f 0) (f 1) (Or.inl rfl))).1,
          directMembershipAtomicHolds_eq (natCast_mem_of_lt (f 0).isLt)
            (natCast_mem_of_lt (f 1).isLt), value_standardTuple, value_standardTuple]
        rfl
      · obtain ⟨f, rfl⟩ := setSemiterms_eq_bvars ts
        rw [encodeMembershipFormula_rel_bvar _ f (t := (1 : V)) rfl,
          (h.2.1 _ _ (membershipAtomicArguments_pair (f 0) (f 1) (Or.inr rfl))).1,
          directMembershipAtomicHolds_mem (natCast_mem_of_lt (f 0).isLt)
            (natCast_mem_of_lt (f 1).isLt), value_standardTuple, value_standardTuple]
        rfl
    | @nrel m k r ts =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      cases r
      · obtain ⟨f, rfl⟩ := setSemiterms_eq_bvars ts
        rw [encodeMembershipFormula_nrel_bvar _ f (t := (0 : V)) rfl,
          (h.2.1 _ _ (membershipAtomicArguments_pair (f 0) (f 1) (Or.inl rfl))).2,
          directMembershipAtomicHolds_eq (natCast_mem_of_lt (f 0).isLt)
            (natCast_mem_of_lt (f 1).isLt), value_standardTuple, value_standardTuple]
        rfl
      · obtain ⟨f, rfl⟩ := setSemiterms_eq_bvars ts
        rw [encodeMembershipFormula_nrel_bvar _ f (t := (1 : V)) rfl,
          (h.2.1 _ _ (membershipAtomicArguments_pair (f 0) (f 1) (Or.inr rfl))).2,
          directMembershipAtomicHolds_mem (natCast_mem_of_lt (f 0).isLt)
            (natCast_mem_of_lt (f 1).isLt), value_standardTuple, value_standardTuple]
        rfl
    | @and m φ ψ ihφ ihψ =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      rw [show encodeMembershipFormula (V := V) (Semiformula.and φ ψ) =
        andCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ) from rfl,
        (h.2.2.1 _ _ (isMembershipFormulaCode_encode φ) (isMembershipFormulaCode_encode ψ)).1]
      exact and_congr (ihφ c) (ihψ c)
    | @or m φ ψ ihφ ihψ =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      rw [show encodeMembershipFormula (V := V) (Semiformula.or φ ψ) =
        orCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ) from rfl,
        (h.2.2.1 _ _ (isMembershipFormulaCode_encode φ) (isMembershipFormulaCode_encode ψ)).2]
      exact or_congr (ihφ c) (ihψ c)
    | @all m φ ih =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      have hcode : IsMembershipFormulaCode (succ (m : V)) (encodeMembershipFormula φ) := by
        have hc := isMembershipFormulaCode_encode (V := V) φ
        rwa [num_succ_def] at hc
      rw [show encodeMembershipFormula (V := V) (Semiformula.all φ) = allCode (encodeMembershipFormula φ) from rfl,
        (h.2.2.2 _ hcode).1]
      constructor
      · intro hall x
        have hx := hall x
        rw [← standardTuple_cons, ← num_succ_def] at hx
        exact (ih (x :> c)).mp hx
      · intro hall x
        rw [← standardTuple_cons, ← num_succ_def]
        exact (ih (x :> c)).mpr (hall x)
    | @exs m φ ih =>
      intro c
      have h := hS (m : V) (by simp) (standardTuple c) (standardTuple_isFunction c)
        (domain_standardTuple c)
      have hcode : IsMembershipFormulaCode (succ (m : V)) (encodeMembershipFormula φ) := by
        have hc := isMembershipFormulaCode_encode (V := V) φ
        rwa [num_succ_def] at hc
      rw [show encodeMembershipFormula (V := V) (Semiformula.exs φ) = existsCode (encodeMembershipFormula φ) from rfl,
        (h.2.2.2 _ hcode).2]
      constructor
      · rintro ⟨x, hx⟩
        rw [← standardTuple_cons, ← num_succ_def] at hx
        exact ⟨x, (ih (x :> c)).mp hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← standardTuple_cons, ← num_succ_def]; exact (ih (x :> c)).mpr hx⟩
  exact key φ b

/-- Reads "the sentence with Godel number `x` is not in `S`", written with the parameter-free
formula `σ` that is assumed to define `S`. -/
def unsatisfiedSentenceCode (σ : SetTheorySemisentence 3) : SetTheorySemisentence 1 :=
  “x. ∀ y, !decodedNaturalFormulaFormula y x → ∀ z, !(quoteNumeralFormula 0) z → ¬ !σ z y z”

theorem eval_unsatisfiedSentenceCode {S : V → V → V → Prop} {σ : SetTheorySemisentence 3}
    (hσ : ℒₛₑₜ-relation₃[V] S via σ) (x : V) :
    (unsatisfiedSentenceCode σ).Evalb ![x] ↔ ¬ S 0 (decodedNaturalFormula x) 0 := by
  haveI := hσ
  simp [unsatisfiedSentenceCode, eval_quoteNumeralFormula]

/-- Tarski's diagonal argument: no parameter-free formula defines a full satisfaction class.
This is weaker than undefinability with set parameters. -/
theorem no_parameterFree_definable_fullSatisfactionClass {S : V → V → V → Prop}
    (hS : IsFullSatisfactionClass V S) (σ : SetTheorySemisentence 3) :
    ¬ (ℒₛₑₜ-relation₃[V] S via σ) := by
  intro hσ
  have hfix := models_setFixedpoint (V := V) (unsatisfiedSentenceCode σ)
  rw [eval_unsatisfiedSentenceCode hσ] at hfix
  set τ := setFixedpoint (unsatisfiedSentenceCode σ) with hτ
  rw [decodedNaturalFormula_membership τ] at hfix
  have heval := hS.evalb_iff τ (![] : Fin 0 → V)
  have hz : ((0 : ℕ) : V) = (0 : V) := by simp
  have hst : standardTuple (![] : Fin 0 → V) = (0 : V) := by simp [standardTuple, zero_def]
  rw [hz, hst] at heval
  rw [heval] at hfix
  have hm : Semiformula.Evalb (![] : Fin 0 → V) τ ↔ V↓[ℒₛₑₜ] ⊧ τ := Iff.rfl
  rw [hm] at hfix
  exact iff_not_self hfix

end ZFVP
