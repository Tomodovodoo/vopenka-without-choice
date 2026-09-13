import ZFVP.Syntax.EndExtensionMembershipSyntax
import ZFVP.ModelTheory.TarskiUndefinability
import ZFVP.ModelTheory.ConservativeRankExtension
import ZFVP.ModelTheory.DirectedElementaryUnion
import ZFVP.ModelTheory.CodedSequentSemantics
import ZFVP.ModelTheory.EndExtensionLanguage
import ZFVP.Syntax.EndExtensionFormulas
import ZFVP.Syntax.EndExtensionAssignments

/-! Case I of Enayat's Theorem 4.4(b) in "Models of set theory: extensions and dead ends",
in the conservative case.

Let `j : V → W` be an end extension of models of ZF and let `hierarchy δ` be a rank stage of `W`
that contains the whole image of `V` and in which that image behaves like an elementary
submodel for the internally coded formulas. Pulling the satisfaction relation of the stage back
along `j` gives a full satisfaction class for `V`. If `j` is conservative, that pullback is
definable in `V`, which Tarski's undefinability theorem rules out. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Transport of the membership language and of atomic syntax -/

theorem map_constantGraph' (j : MembershipEndExtension V W) (A a : V) :
    j (constantGraph A a) = constantGraph (j A) (j a) :=
  j.map_definableGraph A (fun _ ↦ a) (fun _ ↦ j a) (by definability) (by definability)
    (fun _ _ ↦ rfl)

theorem map_membershipLanguageCode' (j : MembershipEndExtension V W) :
    j (membershipLanguageCode : V) = (membershipLanguageCode : W) := by
  have h2 : j (2 : V) = (2 : W) := j.map_numeral 2
  simp only [membershipLanguageCode, j.map_languageCode, j.map_constantGraph', j.map_empty, h2]

theorem map_boundVarCode' (j : MembershipEndExtension V W) (i : V) :
    j (boundVarCode i) = boundVarCode (j i) := by
  unfold boundVarCode
  rw [j.map_kpair, show j (0 : V) = (0 : W) from j.map_numeral 0]

/-- Membership formula codes travel along an end extension. -/
theorem map_isMembershipFormulaCode (j : MembershipEndExtension V W) {n φ : V}
    (h : IsMembershipFormulaCode n φ) : IsMembershipFormulaCode (j n) (j φ) := by
  unfold IsMembershipFormulaCode at h ⊢
  rw [← j.map_membershipLanguageCode', ← j.map_empty,
    ← j.map_formulaFamily membershipLanguageCode_valid ∅, ← j.map_kpair]
  exact (j.mem_iff _ _).mpr h

theorem map_mem_membershipFormulaSet (j : MembershipEndExtension V W) {n φ : V}
    (h : φ ∈ formulaSet (membershipLanguageCode : V) ∅ n) :
    j φ ∈ formulaSet (membershipLanguageCode : W) ∅ (j n) := by
  rw [← j.map_membershipLanguageCode', ← j.map_empty,
    ← j.map_formulaSet membershipLanguageCode_valid ∅ n]
  exact (j.mem_iff _ _).mpr h

theorem map_isMembershipAtomicArguments (j : MembershipEndExtension V W) {n r args : V}
    (h : IsMembershipAtomicArguments n r args) :
    IsMembershipAtomicArguments (j n) (j r) (j args) := by
  obtain ⟨hr, i, hi, k, hk, rfl⟩ := h
  refine ⟨?_, j i, (j.mem_iff i n).mpr hi, j k, (j.mem_iff k n).mpr hk,
    j.map_boundPairArguments i k⟩
  rcases hr with rfl | rfl | rfl
  · exact Or.inl j.map_equalityToken
  · exact Or.inr (Or.inl (by rw [j.map_relationToken, show j (0 : V) = (0 : W) from j.map_numeral 0]))
  · exact Or.inr (Or.inr (by rw [j.map_relationToken, show j (1 : V) = (1 : W) from j.map_numeral 1]))

/-- Atomic truth is the same computed in the smaller model and in the image. -/
theorem map_directMembershipAtomicHolds (j : MembershipEndExtension V W) {n b r args : V}
    [IsFunction b] (hd : domain b = n) (ha : IsMembershipAtomicArguments n r args) :
    DirectMembershipAtomicHolds (j n) (j b) (j r) (j args) ↔
      DirectMembershipAtomicHolds n b r args := by
  obtain ⟨-, i, hi, k, hk, rfl⟩ := ha
  have hid : i ∈ domain b := by rw [hd]; exact hi
  have hkd : k ∈ domain b := by rw [hd]; exact hk
  have hvi : j (b ‘ i) = (j b) ‘ (j i) := j.map_value b i hid
  have hvk : j (b ‘ k) = (j b) ‘ (j k) := j.map_value b k hkd
  have heq : (j b) ‘ (j i) = (j b) ‘ (j k) ↔ b ‘ i = b ‘ k := by
    rw [← hvi, ← hvk, j.injective.eq_iff]
  have hmem : (j b) ‘ (j i) ∈ (j b) ‘ (j k) ↔ b ‘ i ∈ b ‘ k := by
    rw [← hvi, ← hvk, j.mem_iff]
  have hr0 : j r = equalityToken ↔ r = equalityToken := by
    rw [← j.map_equalityToken, j.injective.eq_iff]
  have hr1 : j r = relationToken (0 : W) ↔ r = relationToken (0 : V) := by
    rw [show relationToken (0 : W) = j (relationToken (0 : V)) by
      rw [j.map_relationToken, show j (0 : V) = (0 : W) from j.map_numeral 0],
      j.injective.eq_iff]
  have hr2 : j r = relationToken (1 : W) ↔ r = relationToken (1 : V) := by
    rw [show relationToken (1 : W) = j (relationToken (1 : V)) by
      rw [j.map_relationToken, show j (1 : V) = (1 : W) from j.map_numeral 1],
      j.injective.eq_iff]
  constructor
  · rintro ⟨i', hi', k', hk', hargs, hcase⟩
    rw [j.map_boundPairArguments] at hargs
    obtain ⟨rfl, rfl⟩ := boundPairArguments_inj.mp hargs
    refine ⟨i, hi, k, hk, rfl, ?_⟩
    rcases hcase with ⟨hs, he⟩ | ⟨hs, hm⟩
    · exact Or.inl ⟨hs.imp hr0.mp hr1.mp, heq.mp he⟩
    · exact Or.inr ⟨hr2.mp hs, hmem.mp hm⟩
  · rintro ⟨i', hi', k', hk', hargs, hcase⟩
    obtain ⟨rfl, rfl⟩ := boundPairArguments_inj.mp hargs
    refine ⟨j i, (j.mem_iff i n).mpr hi, j k, (j.mem_iff k n).mpr hk,
      j.map_boundPairArguments i k, ?_⟩
    rcases hcase with ⟨hs, he⟩ | ⟨hs, hm⟩
    · exact Or.inl ⟨hs.imp hr0.mpr hr1.mpr, heq.mpr he⟩
    · exact Or.inr ⟨hr2.mpr hs, hmem.mpr hm⟩

end MembershipEndExtension

/-! ### The remaining clauses of set-coded satisfaction -/

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipSatisfies_truthCode {A n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n truthCode b := by
  have h : Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n truthCode b ↔
      b ∈ structureDomain (membershipStructureCode A) ^ n :=
    satisfies_truth membershipLanguageCode_valid hn
  rw [membershipStructureCode_domain] at h
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies] using h.mpr hb

theorem not_membershipSatisfies_falsityCode {A n b : V} (hn : n ∈ (ω : V)) :
    ¬ MembershipSatisfies A n falsityCode b := by
  have h : ¬ Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n falsityCode b :=
    not_satisfies_falsity membershipLanguageCode_valid hn
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies] using h

theorem membershipSatisfies_atomCode {A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsMembershipAtomicArguments n r args) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args := by
  have h : Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n (atomCode r args) b ↔
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args :=
    satisfies_atom membershipLanguageCode_valid hn ((membershipAtomicArguments_iff hn).mpr ha)
      (by simpa using hb)
  rw [← directMembershipAtomicHolds_iff hn hb ha] at h
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies] using h

theorem membershipSatisfies_negAtomCode {A n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsMembershipAtomicArguments n r args) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (negAtomCode r args) b ↔ ¬ DirectMembershipAtomicHolds n b r args := by
  have h : Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n
        (negAtomCode r args) b ↔
      ¬ AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args :=
    satisfies_negAtom membershipLanguageCode_valid hn ((membershipAtomicArguments_iff hn).mpr ha)
      (by simpa using hb)
  rw [← directMembershipAtomicHolds_iff hn hb ha] at h
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies] using h

/-! ### The pulled back satisfaction relation of a rank stage -/

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The satisfaction relation of the rank stage `hierarchy δ` of `W`, pulled back along `j`. -/
def stageSatisfaction (j : MembershipEndExtension V W) (δ : W) : V → V → V → Prop :=
  fun n φ b ↦ MembershipSatisfies (hierarchy δ) (j n) (j φ) (j b)

/-- If the stage contains the image of `V`, then an assignment of `V` maps to an assignment of the
stage. -/
theorem mem_stage_function {j : MembershipEndExtension V W} {δ : W}
    (hsub : ∀ x : V, j x ∈ hierarchy δ) {n b : V} [IsFunction b] (hd : domain b = n) :
    j b ∈ (hierarchy δ) ^ (j n) := by
  obtain ⟨X, Y, hbXY⟩ := isFunction_def.mp ‹IsFunction b›
  have hX : X = n := by rw [← domain_eq_of_mem_function hbXY, hd]
  rw [hX] at hbXY
  have hjbr : j b ∈ (j Y) ^ (j n) := (j.function_iff b n Y).mpr hbXY
  refine mem_function_of_mem_function_of_subset hjbr ?_
  intro y hy
  obtain ⟨z, _, rfl⟩ := j.endExtension _ y hy
  exact hsub z

/-- Enayat's Theorem 4.4(b), Case I. If the image of `V` sits inside the rank stage `hierarchy δ`
of `W` and satisfies the Tarski test there for the internally coded formulas, then the stage's
satisfaction relation pulled back along `j` is a full satisfaction class for `V`. -/
theorem stageSatisfaction_isFullSatisfactionClass (j : MembershipEndExtension V W) (δ : W)
    (hsub : ∀ x : V, j x ∈ hierarchy δ)
    (helem : ∀ n φ b : V, IsMembershipFormulaCode (succ n) φ → IsFunction b → domain b = n →
      ((∀ y : V, MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) →
          ∀ x : W, x ∈ hierarchy δ →
            MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) ∧
      ((∃ x : W, x ∈ hierarchy δ ∧
            MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) →
          ∃ y : V, MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y)))) :
    IsFullSatisfactionClass V (stageSatisfaction j δ) := by
  intro n hn b hbf hbd
  have : IsFunction b := hbf
  have hjn : j n ∈ (ω : W) := (j.natural_iff n).mpr hn
  have hjb : j b ∈ (hierarchy δ) ^ (j n) := mem_stage_function hsub hbd
  simp only [stageSatisfaction]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [j.map_truthCode]
    exact membershipSatisfies_truthCode hjn hjb
  · rw [j.map_falsityCode]
    exact not_membershipSatisfies_falsityCode hjn
  · intro r args ha
    have hja := j.map_isMembershipAtomicArguments ha
    constructor
    · rw [j.map_atomCode, membershipSatisfies_atomCode hjn hja hjb]
      exact j.map_directMembershipAtomicHolds hbd ha
    · rw [j.map_negAtomCode, membershipSatisfies_negAtomCode hjn hja hjb]
      exact not_congr (j.map_directMembershipAtomicHolds hbd ha)
  · intro φ ψ hφ hψ
    have hjφ := j.map_mem_membershipFormulaSet hφ.valid
    have hjψ := j.map_mem_membershipFormulaSet hψ.valid
    constructor
    · rw [j.map_andCode]
      exact membershipSatisfies_and hjn hjφ hjψ hjb
    · rw [j.map_orCode]
      exact membershipSatisfies_or hjn hjφ hjψ hjb
  · intro φ hφ
    have hjφ : j φ ∈ formulaSet (membershipLanguageCode : W) ∅ (succ (j n)) := by
      have h := j.map_mem_membershipFormulaSet hφ.valid
      rwa [j.map_succ] at h
    have hstep : ∀ x : V, j (assignmentPrepend n b x) = assignmentPrepend (j n) (j b) (j x) :=
      fun x ↦ j.map_assignmentPrepend n b x
    obtain ⟨hall, hex⟩ := helem n φ b hφ hbf hbd
    constructor
    · rw [j.map_allCode, membershipSatisfies_all hjn hjφ hjb]
      constructor
      · intro h x
        rw [j.map_succ, hstep x]
        exact h (j x) (hsub x)
      · intro h x hx
        refine hall (fun y ↦ ?_) x hx
        have hy := h y
        rwa [j.map_succ, hstep y] at hy
    · rw [j.map_existsCode, membershipSatisfies_exists hjn hjφ hjb]
      constructor
      · rintro ⟨x, hx, hbody⟩
        obtain ⟨y, hy⟩ := hex ⟨x, hx, hbody⟩
        exact ⟨y, by rw [j.map_succ, hstep y]; exact hy⟩
      · rintro ⟨x, hx⟩
        rw [j.map_succ, hstep x] at hx
        exact ⟨j x, hsub x, hx⟩

/-- Along a conservative end extension the pulled back satisfaction relation of a rank stage is
definable in the smaller model. -/
theorem stageSatisfaction_definable {j : MembershipEndExtension V W} (h : j.IsConservative)
    (δ : W) : ℒₛₑₜ-relation₃[V] (stageSatisfaction j δ) := by
  have hD : ℒₛₑₜ-predicate[W] (fun w : W ↦ ∃ n φ b : W, w = ⟨n, ⟨φ, b⟩ₖ⟩ₖ ∧
      MembershipSatisfies (hierarchy δ) n φ b) := by definability
  have hpull : ℒₛₑₜ-predicate[V] (fun x : V ↦ ∃ n φ b : W, j x = ⟨n, ⟨φ, b⟩ₖ⟩ₖ ∧
      MembershipSatisfies (hierarchy δ) n φ b) := h _ hD
  have hf : ℒₛₑₜ-function₃[V] (fun n φ b : V ↦ ⟨n, ⟨φ, b⟩ₖ⟩ₖ) := by definability
  have hdef : ℒₛₑₜ-relation₃[V] (fun n φ b : V ↦ ∃ n' φ' b' : W, j ⟨n, ⟨φ, b⟩ₖ⟩ₖ = ⟨n', ⟨φ', b'⟩ₖ⟩ₖ ∧
      MembershipSatisfies (hierarchy δ) n' φ' b') :=
    Language.DefinablePred.comp (hP := hpull) hf
  refine Language.Definable.of_iff hdef (fun v ↦ ?_)
  change stageSatisfaction j δ (v 0) (v 1) (v 2) ↔ _
  unfold stageSatisfaction
  constructor
  · intro hs
    exact ⟨j (v 0), j (v 1), j (v 2), by rw [j.map_kpair, j.map_kpair], hs⟩
  · rintro ⟨n', φ', b', he, hs⟩
    rw [j.map_kpair, j.map_kpair] at he
    obtain ⟨rfl, he'⟩ := kpair_inj he
    obtain ⟨rfl, rfl⟩ := kpair_inj he'
    exact hs

/-- Enayat's Theorem 4.4(b), Case I, in the conservative case: a conservative end extension of a
model of ZF has no rank stage that contains the image of the model and in which that image passes
the Tarski test. -/
theorem false_of_elementary_stage {j : MembershipEndExtension V W} (h : j.IsConservative) (δ : W)
    (hsub : ∀ x : V, j x ∈ hierarchy δ)
    (helem : ∀ n φ b : V, IsMembershipFormulaCode (succ n) φ → IsFunction b → domain b = n →
      ((∀ y : V, MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) →
          ∀ x : W, x ∈ hierarchy δ →
            MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) ∧
      ((∃ x : W, x ∈ hierarchy δ ∧
            MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) →
          ∃ y : V, MembershipSatisfies (hierarchy δ) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y)))) :
    False :=
  no_definable_fullSatisfactionClass (stageSatisfaction j δ)
    (stageSatisfaction_isFullSatisfactionClass j δ hsub helem)
    (stageSatisfaction_definable h δ)

end ZFVP
