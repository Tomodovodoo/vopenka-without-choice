import ZFVP.SetTheory.UltrapowerLosAtomic
import ZFVP.SetTheory.UltrapowerWitness
import ZFVP.Syntax.FormulaInduction
import ZFVP.Syntax.SatisfactionEquations
import ZFVP.Syntax.MembershipSwap

/-! Los's theorem for the internal ultrapower.

Fix a transitive set `A`, an index set `P` and an ultrafilter `U` on `P` that is complete enough for
the a.e. membership relation on `A ^ P` to be internally well founded. An assignment for the
ultrapower is a function `b ∈ (A ^ P) ^ n`. Composing it with the collapse map gives an assignment
into the collapsed set `ultraTarget P U A`; evaluating it at an index `p ∈ P` gives an assignment
into `A`. The theorem says that a coded formula holds of the composed assignment in the collapsed
set exactly when the set of indices where it holds of the pointwise assignment is in `U`.

The proof is the definable induction over the coded formula family. The atomic clauses are already
done in `ZFVP.SetTheory.UltrapowerLosAtomic`. The propositional clauses come from the index set of a
conjunction being an intersection and the index set of a disjunction a union. The quantifier clauses
are where the ultrafilter does work: an existential witness in the collapsed set is the collapse of
some function on `P`, and going the other way a witness at each index of a set in `U` is glued into
one function by `exists_ultraFunction_of_witnesses`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The satisfaction clauses in the membership language

`MembershipSatisfies A n φ b` is `Satisfies` for the membership language code at the structure code
of `A`, so the eight generic clauses apply with the structure domain read off as `A`. -/

theorem membershipSatisfies_iff_satisfies (A n φ b : V) :
    MembershipSatisfies A n φ b ↔
      Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n φ b :=
  Iff.rfl

theorem membershipSatisfies_truth {A n b : V} (hn : n ∈ (ω : V)) :
    MembershipSatisfies A n truthCode b ↔ b ∈ A ^ n := by
  simp only [membershipSatisfies_iff_satisfies]
  rw [satisfies_truth (Γ := (∅ : V)) membershipLanguageCode_valid hn,
    membershipStructureCode_domain]

theorem not_membershipSatisfies_falsity {A n b : V} (hn : n ∈ (ω : V)) :
    ¬MembershipSatisfies A n falsityCode b := by
  simp only [membershipSatisfies_iff_satisfies]
  exact not_satisfies_falsity (Γ := (∅ : V)) membershipLanguageCode_valid hn

theorem membershipSatisfies_atom {A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (atomCode r args) b ↔
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args := by
  simp only [membershipSatisfies_iff_satisfies]
  exact satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hb)

theorem membershipSatisfies_negAtom {A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (negAtomCode r args) b ↔
      ¬AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args := by
  simp only [membershipSatisfies_iff_satisfies]
  exact satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hb)

theorem ultraMembershipSatisfies_and {A n b φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (andCode φ ψ) b ↔
      MembershipSatisfies A n φ b ∧ MembershipSatisfies A n ψ b := by
  simp only [membershipSatisfies_iff_satisfies]
  exact satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hb)

theorem ultraMembershipSatisfies_or {A n b φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (orCode φ ψ) b ↔
      MembershipSatisfies A n φ b ∨ MembershipSatisfies A n ψ b := by
  simp only [membershipSatisfies_iff_satisfies]
  exact satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hb)

theorem membershipSatisfies_allCode {A n b φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (allCode φ) b ↔
      ∀ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  simp only [membershipSatisfies_iff_satisfies]
  rw [satisfies_all membershipLanguageCode_valid hn hφ (by simpa using hb),
    membershipStructureCode_domain]

theorem membershipSatisfies_existsCode {A n b φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (existsCode φ) b ↔
      ∃ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  simp only [membershipSatisfies_iff_satisfies]
  rw [satisfies_exists membershipLanguageCode_valid hn hφ (by simpa using hb),
    membershipStructureCode_domain]

/-! ### The index set of a formula -/

/-- The set of indices at which a formula holds of the pointwise assignment. -/
noncomputable def losSet (P A n φ b : V) : V :=
  {p ∈ P ; MembershipSatisfies A n φ (pointwiseAssignment n b p)}

theorem mem_losSet_iff {P A n φ b p : V} :
    p ∈ losSet P A n φ b ↔ p ∈ P ∧ MembershipSatisfies A n φ (pointwiseAssignment n b p) := by
  rw [losSet, mem_sep_iff]

theorem losSet_subset (P A n φ b : V) : losSet P A n φ b ⊆ P :=
  fun _ hp ↦ (mem_losSet_iff.mp hp).1

/-- The index set spelled out by its defining property, for use inside definability proofs. -/
theorem losSet_mem_iff_exists {P A n φ b U : V} :
    losSet P A n φ b ∈ U ↔ ∃ Y, (∀ p, p ∈ Y ↔
      p ∈ P ∧ MembershipSatisfies A n φ (pointwiseAssignment n b p)) ∧ Y ∈ U := by
  constructor
  · intro h
    exact ⟨_, fun _ ↦ mem_losSet_iff, h⟩
  · rintro ⟨Y, hY, hYU⟩
    have hYeq : Y = losSet P A n φ b := by
      apply mem_ext
      intro p
      rw [hY p, mem_losSet_iff]
    exact hYeq ▸ hYU

/-! ### The index set of each shape of formula -/

theorem losSet_truthCode {P A n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ (A ^ P) ^ n) :
    losSet P A n truthCode b = P := by
  apply mem_ext
  intro p
  rw [mem_losSet_iff]
  refine ⟨fun h ↦ h.1, fun hp ↦ ⟨hp, ?_⟩⟩
  exact (membershipSatisfies_truth hn).mpr (pointwiseAssignment_mem_function hb hp)

theorem losSet_falsityCode {P A n b : V} (hn : n ∈ (ω : V)) :
    losSet P A n falsityCode b = ∅ := by
  apply mem_ext
  intro p
  constructor
  · intro h
    exact absurd (mem_losSet_iff.mp h).2 (not_membershipSatisfies_falsity hn)
  · intro h
    exact absurd h not_mem_empty

theorem losSet_atomCode {P A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ (A ^ P) ^ n) :
    losSet P A n (atomCode r args) b = atomicLosSet P A n b r args := by
  apply mem_ext
  intro p
  rw [mem_losSet_iff, mem_atomicLosSet_iff]
  exact and_congr_right fun hp ↦
    membershipSatisfies_atom hn ha (pointwiseAssignment_mem_function hb hp)

theorem losSet_negAtomCode {P A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ (A ^ P) ^ n) :
    losSet P A n (negAtomCode r args) b =
      relativeComplement P (atomicLosSet P A n b r args) := by
  apply mem_ext
  intro p
  rw [mem_losSet_iff, mem_relativeComplement_iff]
  refine and_congr_right fun hp ↦ ?_
  rw [membershipSatisfies_negAtom hn ha (pointwiseAssignment_mem_function hb hp)]
  apply not_congr
  rw [mem_atomicLosSet_iff]
  exact (and_iff_right hp).symm

theorem losSet_andCode {P A n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (A ^ P) ^ n) :
    losSet P A n (andCode φ ψ) b = losSet P A n φ b ∩ losSet P A n ψ b := by
  apply mem_ext
  intro p
  rw [mem_inter_iff, mem_losSet_iff, mem_losSet_iff, mem_losSet_iff]
  constructor
  · rintro ⟨hp, h⟩
    obtain ⟨h1, h2⟩ :=
      (ultraMembershipSatisfies_and hn hφ hψ (pointwiseAssignment_mem_function hb hp)).mp h
    exact ⟨⟨hp, h1⟩, hp, h2⟩
  · rintro ⟨⟨hp, h1⟩, _, h2⟩
    exact ⟨hp, (ultraMembershipSatisfies_and hn hφ hψ
      (pointwiseAssignment_mem_function hb hp)).mpr ⟨h1, h2⟩⟩

theorem losSet_orCode {P A n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (A ^ P) ^ n) :
    losSet P A n (orCode φ ψ) b = losSet P A n φ b ∪ losSet P A n ψ b := by
  apply mem_ext
  intro p
  rw [mem_union_iff, mem_losSet_iff, mem_losSet_iff, mem_losSet_iff]
  constructor
  · rintro ⟨hp, h⟩
    rcases (ultraMembershipSatisfies_or hn hφ hψ (pointwiseAssignment_mem_function hb hp)).mp h with
      h1 | h2
    · exact Or.inl ⟨hp, h1⟩
    · exact Or.inr ⟨hp, h2⟩
  · rintro (⟨hp, h1⟩ | ⟨hp, h2⟩)
    · exact ⟨hp, (ultraMembershipSatisfies_or hn hφ hψ
        (pointwiseAssignment_mem_function hb hp)).mpr (Or.inl h1)⟩
    · exact ⟨hp, (ultraMembershipSatisfies_or hn hφ hψ
        (pointwiseAssignment_mem_function hb hp)).mpr (Or.inr h2)⟩

/-- Membership in the index set of a formula whose assignment has one value prepended. -/
theorem mem_losSet_prepend_iff {P A n φ b k p : V} (hn : n ∈ (ω : V)) (hb : b ∈ (A ^ P) ^ n)
    (hk : k ∈ A ^ P) (hp : p ∈ P) :
    p ∈ losSet P A (succ n) φ (assignmentPrepend n b k) ↔
      MembershipSatisfies A (succ n) φ
        (assignmentPrepend n (pointwiseAssignment n b p) (k ‘ p)) := by
  rw [mem_losSet_iff, pointwiseAssignment_prepend hn hb hk hp]
  exact and_iff_right hp

/-! ### Intersections in an ultrafilter -/

theorem inter_mem_ultrafilter_iff {P U X Y : V} (hU : IsSetUltrafilter P U) (hX : X ⊆ P)
    (hY : Y ⊆ P) : X ∩ Y ∈ U ↔ X ∈ U ∧ Y ∈ U := by
  constructor
  · intro h
    exact ⟨hU.upward h hX fun z hz ↦ (mem_inter_iff.mp hz).1,
      hU.upward h hY fun z hz ↦ (mem_inter_iff.mp hz).2⟩
  · rintro ⟨h1, h2⟩
    exact hU.inter h1 h2

/-! ### The two families of witnesses used by the quantifier clauses -/

/-- The members of `A` that make the body of an existential true at the index `p`. -/
noncomputable def losWitnessSet (A n φ b p : V) : V :=
  {z ∈ A ; MembershipSatisfies A (succ n) φ (assignmentPrepend n (pointwiseAssignment n b p) z)}

theorem mem_losWitnessSet_iff {A n φ b p z : V} :
    z ∈ losWitnessSet A n φ b p ↔ z ∈ A ∧
      MembershipSatisfies A (succ n) φ
        (assignmentPrepend n (pointwiseAssignment n b p) z) := by
  rw [losWitnessSet, mem_sep_iff]

theorem losWitnessSet_subset (A n φ b p : V) : losWitnessSet A n φ b p ⊆ A :=
  fun _ hz ↦ (mem_losWitnessSet_iff.mp hz).1

theorem losWitnessSet_definable_one (A n φ b : V) :
    ℒₛₑₜ-function₁[V] (losWitnessSet A n φ b) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y p ↦ ∀ z, z ∈ Y ↔ z ∈ A ∧
      MembershipSatisfies A (succ n) φ
        (assignmentPrepend n (pointwiseAssignment n b p) z)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = losWitnessSet A n φ b (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [losWitnessSet, mem_sep_iff]

/-- The members of `A` that make the body of a universal false at the index `p`. -/
noncomputable def losFailureSet (A n φ b p : V) : V :=
  {z ∈ A ; ¬MembershipSatisfies A (succ n) φ (assignmentPrepend n (pointwiseAssignment n b p) z)}

theorem mem_losFailureSet_iff {A n φ b p z : V} :
    z ∈ losFailureSet A n φ b p ↔ z ∈ A ∧
      ¬MembershipSatisfies A (succ n) φ
        (assignmentPrepend n (pointwiseAssignment n b p) z) := by
  rw [losFailureSet, mem_sep_iff]

theorem losFailureSet_subset (A n φ b p : V) : losFailureSet A n φ b p ⊆ A :=
  fun _ hz ↦ (mem_losFailureSet_iff.mp hz).1

theorem losFailureSet_definable_one (A n φ b : V) :
    ℒₛₑₜ-function₁[V] (losFailureSet A n φ b) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y p ↦ ∀ z, z ∈ Y ↔ z ∈ A ∧
      ¬MembershipSatisfies A (succ n) φ
        (assignmentPrepend n (pointwiseAssignment n b p) z)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = losFailureSet A n φ b (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [losFailureSet, mem_sep_iff]

/-! ### The quantifier clauses on the index side -/

/-- An existential holds a.e. exactly when some single function on the index set witnesses it
a.e. One direction is upward closure, the other glues pointwise witnesses into one function. -/
theorem losSet_existsCode_iff (hAC : InternalChoice V) {P U A n φ b : V}
    (hU : IsSetUltrafilter P U) (hA : IsNonempty A) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (A ^ P) ^ n) :
    (∃ k, k ∈ A ^ P ∧ losSet P A (succ n) φ (assignmentPrepend n b k) ∈ U) ↔
      losSet P A n (existsCode φ) b ∈ U := by
  constructor
  · rintro ⟨k, hk, hkU⟩
    refine hU.upward hkU (losSet_subset P A n (existsCode φ) b) ?_
    intro p hp
    have hpP : p ∈ P := losSet_subset P A (succ n) φ (assignmentPrepend n b k) p hp
    have hs := (mem_losSet_prepend_iff hn hb hk hpP).mp hp
    refine mem_losSet_iff.mpr ⟨hpP, ?_⟩
    exact (membershipSatisfies_existsCode hn hφ
      (pointwiseAssignment_mem_function hb hpP)).mpr ⟨k ‘ p, function_value_mem hk hpP, hs⟩
  · intro hS
    have hSP : losSet P A n (existsCode φ) b ⊆ P := losSet_subset P A n (existsCode φ) b
    have hne : ∀ p ∈ losSet P A n (existsCode φ) b, IsNonempty (losWitnessSet A n φ b p) := by
      intro p hp
      have hpP : p ∈ P := hSP p hp
      obtain ⟨x, hx, hxs⟩ := (membershipSatisfies_existsCode hn hφ
        (pointwiseAssignment_mem_function hb hpP)).mp (mem_losSet_iff.mp hp).2
      exact ⟨⟨x, mem_losWitnessSet_iff.mpr ⟨hx, hxs⟩⟩⟩
    obtain ⟨k, hk, hkval⟩ :=
      exists_ultraFunction_of_witnesses hAC hSP hA (losWitnessSet A n φ b)
        (losWitnessSet_definable_one A n φ b) (fun p _ ↦ losWitnessSet_subset A n φ b p) hne
    refine ⟨k, hk, ?_⟩
    refine hU.upward hS (losSet_subset P A (succ n) φ (assignmentPrepend n b k)) ?_
    intro p hp
    exact (mem_losSet_prepend_iff hn hb hk (hSP p hp)).mpr
      (mem_losWitnessSet_iff.mp (hkval p hp)).2

/-- A universal holds a.e. exactly when every function on the index set satisfies the body a.e.
The hard direction picks a counterexample at each index outside the index set of the universal. -/
theorem losSet_allCode_iff (hAC : InternalChoice V) {P U A n φ b : V}
    (hU : IsSetUltrafilter P U) (hA : IsNonempty A) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (A ^ P) ^ n) :
    (∀ k, k ∈ A ^ P → losSet P A (succ n) φ (assignmentPrepend n b k) ∈ U) ↔
      losSet P A n (allCode φ) b ∈ U := by
  constructor
  · intro hall
    by_contra hS
    have hSP : losSet P A n (allCode φ) b ⊆ P := losSet_subset P A n (allCode φ) b
    have hQ : relativeComplement P (losSet P A n (allCode φ) b) ∈ U :=
      (not_mem_ultrafilter_iff_compl hU hSP).mp hS
    have hQP : relativeComplement P (losSet P A n (allCode φ) b) ⊆ P :=
      fun z hz ↦ ((mem_relativeComplement_iff z P (losSet P A n (allCode φ) b)).mp hz).1
    have hne : ∀ p ∈ relativeComplement P (losSet P A n (allCode φ) b),
        IsNonempty (losFailureSet A n φ b p) := by
      intro p hp
      obtain ⟨hpP, hpn⟩ := (mem_relativeComplement_iff p P (losSet P A n (allCode φ) b)).mp hp
      have h : ¬MembershipSatisfies A n (allCode φ) (pointwiseAssignment n b p) :=
        fun hh ↦ hpn (mem_losSet_iff.mpr ⟨hpP, hh⟩)
      rw [membershipSatisfies_allCode hn hφ (pointwiseAssignment_mem_function hb hpP)] at h
      push Not at h
      obtain ⟨x, hx, hxs⟩ := h
      exact ⟨⟨x, mem_losFailureSet_iff.mpr ⟨hx, hxs⟩⟩⟩
    obtain ⟨k, hk, hkval⟩ :=
      exists_ultraFunction_of_witnesses hAC hQP hA (losFailureSet A n φ b)
        (losFailureSet_definable_one A n φ b) (fun p _ ↦ losFailureSet_subset A n φ b p) hne
    obtain ⟨z, hz⟩ := hU.nonempty_of_mem (hU.inter hQ (hall k hk))
    rw [mem_inter_iff] at hz
    exact (mem_losFailureSet_iff.mp (hkval z hz.1)).2
      ((mem_losSet_prepend_iff hn hb hk (hQP z hz.1)).mp hz.2)
  · intro hS k hk
    refine hU.upward hS (losSet_subset P A (succ n) φ (assignmentPrepend n b k)) ?_
    intro p hp
    have hpP : p ∈ P := losSet_subset P A n (allCode φ) b p hp
    have h := (mem_losSet_iff.mp hp).2
    rw [membershipSatisfies_allCode hn hφ (pointwiseAssignment_mem_function hb hpP)] at h
    exact (mem_losSet_prepend_iff hn hb hk hpP).mpr (h (k ‘ p) (function_value_mem hk hpP))

/-! ### The quantifier clauses on the collapsed side -/

/-- Every element of the collapsed set is the collapse of a function on the index set, so an
existential over the collapsed set is an existential over `A ^ P`. -/
theorem existsCode_ultraTarget_iff {P U A n φ b : V}
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (A ^ P) ^ n) :
    MembershipSatisfies (ultraTarget P U A) n (existsCode φ) (compose b (ultraCollapse P U A)) ↔
      ∃ k, k ∈ A ^ P ∧ MembershipSatisfies (ultraTarget P U A) (succ n) φ
        (compose (assignmentPrepend n b k) (ultraCollapse P U A)) := by
  have hC := ultraCollapse_mem_function hwf
  have hfun : IsFunction (ultraCollapse P U A) := ultraCollapse_isFunction hwf
  rw [membershipSatisfies_existsCode hn hφ (compose_ultraCollapse_mem_function hwf hb)]
  constructor
  · rintro ⟨z, hz, hs⟩
    obtain ⟨k, hkz⟩ := mem_range_iff.mp (show z ∈ range (ultraCollapse P U A) from hz)
    refine ⟨k, (mem_of_mem_functions hC hkz).1, ?_⟩
    rw [compose_assignmentPrepend hn hb hC (mem_of_mem_functions hC hkz).1,
      value_eq_of_kpair_mem hkz]
    exact hs
  · rintro ⟨k, hk, hs⟩
    refine ⟨(ultraCollapse P U A) ‘ k, ultraCollapse_value_mem hwf hk, ?_⟩
    rw [← compose_assignmentPrepend hn hb hC hk]
    exact hs

/-- The same for a universal. -/
theorem allCode_ultraTarget_iff {P U A n φ b : V}
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (A ^ P) ^ n) :
    MembershipSatisfies (ultraTarget P U A) n (allCode φ) (compose b (ultraCollapse P U A)) ↔
      ∀ k, k ∈ A ^ P → MembershipSatisfies (ultraTarget P U A) (succ n) φ
        (compose (assignmentPrepend n b k) (ultraCollapse P U A)) := by
  have hC := ultraCollapse_mem_function hwf
  have hfun : IsFunction (ultraCollapse P U A) := ultraCollapse_isFunction hwf
  rw [membershipSatisfies_allCode hn hφ (compose_ultraCollapse_mem_function hwf hb)]
  constructor
  · intro hs k hk
    rw [compose_assignmentPrepend hn hb hC hk]
    exact hs _ (ultraCollapse_value_mem hwf hk)
  · intro hs z hz
    obtain ⟨k, hkz⟩ := mem_range_iff.mp (show z ∈ range (ultraCollapse P U A) from hz)
    have hk : k ∈ A ^ P := (mem_of_mem_functions hC hkz).1
    have h := hs k hk
    rw [compose_assignmentPrepend hn hb hC hk, value_eq_of_kpair_mem hkz] at h
    exact h

/-! ### Los's theorem -/

/-- Los's theorem: a formula holds of a collapsed assignment in the ultrapower exactly when it holds
of the pointwise assignment on a set in the ultrafilter. -/
theorem los (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ] [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) :
    ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet membershipLanguageCode ∅ n, ∀ b ∈ (A ^ P) ^ n,
      (MembershipSatisfies (ultraTarget P U A) n φ (compose b (ultraCollapse P U A)) ↔
        losSet P A n φ b ∈ U) := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  have hdef : ∀ T C : V, ℒₛₑₜ-relation[V] (fun n φ ↦ ∀ b, b ∈ (A ^ P) ^ n →
      (MembershipSatisfies T n φ (compose b C) ↔ losSet P A n φ b ∈ U)) := by
    intro T C
    have hd : ℒₛₑₜ-relation[V] (fun n φ ↦ ∀ b, b ∈ (A ^ P) ^ n →
        (MembershipSatisfies T n φ (compose b C) ↔ ∃ Y, (∀ p, p ∈ Y ↔
          p ∈ P ∧ MembershipSatisfies A n φ (pointwiseAssignment n b p)) ∧ Y ∈ U)) := by
      definability
    apply Language.Definable.of_iff hd
    intro v
    refine forall_congr' fun b ↦ imp_congr_right fun _ ↦ ?_
    exact iff_congr Iff.rfl losSet_mem_iff_exists
  have hmain : ∀ n φ, φ ∈ formulaSet membershipLanguageCode ∅ n → ∀ b, b ∈ (A ^ P) ^ n →
      (MembershipSatisfies (ultraTarget P U A) n φ (compose b (ultraCollapse P U A)) ↔
        losSet P A n φ b ∈ U) := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ b, b ∈ (A ^ P) ^ n →
        (MembershipSatisfies (ultraTarget P U A) n φ (compose b (ultraCollapse P U A)) ↔
          losSet P A n φ b ∈ U))
      (hdef (ultraTarget P U A) (ultraCollapse P U A))
    · intro n hn
      constructor
      · intro b hb
        rw [membershipSatisfies_truth hn, losSet_truthCode hn hb]
        exact iff_of_true (compose_ultraCollapse_mem_function hwf hb) (ultraIndex_mem hU)
      · intro b _
        rw [losSet_falsityCode hn]
        exact iff_of_false (not_membershipSatisfies_falsity hn) hU.empty_not_mem
    · intro n hn r args ha
      constructor
      · intro b hb
        rw [membershipSatisfies_atom hn ha (compose_ultraCollapse_mem_function hwf hb),
          losSet_atomCode hn ha hb]
        exact atomicHolds_ultraTarget_iff hAC hU hcomp hω hA hn hb ha
      · intro b hb
        rw [membershipSatisfies_negAtom hn ha (compose_ultraCollapse_mem_function hwf hb),
          losSet_negAtomCode hn ha hb,
          ← not_mem_ultrafilter_iff_compl hU (atomicLosSet_subset P A n b r args)]
        exact not_congr (atomicHolds_ultraTarget_iff hAC hU hcomp hω hA hn hb ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro b hb
        rw [ultraMembershipSatisfies_and hn hφ hψ (compose_ultraCollapse_mem_function hwf hb),
          losSet_andCode hn hφ hψ hb,
          inter_mem_ultrafilter_iff hU (losSet_subset P A n φ b) (losSet_subset P A n ψ b)]
        exact and_congr (ihφ b hb) (ihψ b hb)
      · intro b hb
        rw [ultraMembershipSatisfies_or hn hφ hψ (compose_ultraCollapse_mem_function hwf hb),
          losSet_orCode hn hφ hψ hb,
          union_mem_ultrafilter_iff hU (losSet_subset P A n φ b) (losSet_subset P A n ψ b)]
        exact or_congr (ihφ b hb) (ihψ b hb)
    · intro n hn φ hφ ih
      constructor
      · intro b hb
        rw [allCode_ultraTarget_iff hwf hn hφ hb, ← losSet_allCode_iff hAC hU hA hn hφ hb]
        constructor
        · intro h k hk
          exact (ih _ (assignmentPrepend_mem_function hn hb hk)).mp (h k hk)
        · intro h k hk
          exact (ih _ (assignmentPrepend_mem_function hn hb hk)).mpr (h k hk)
      · intro b hb
        rw [existsCode_ultraTarget_iff hwf hn hφ hb, ← losSet_existsCode_iff hAC hU hA hn hφ hb]
        constructor
        · rintro ⟨k, hk, h⟩
          exact ⟨k, hk, (ih _ (assignmentPrepend_mem_function hn hb hk)).mp h⟩
        · rintro ⟨k, hk, h⟩
          exact ⟨k, hk, (ih _ (assignmentPrepend_mem_function hn hb hk)).mpr h⟩
  intro n _ φ hφ b hb
  exact hmain n φ hφ b hb

end ZFVP
