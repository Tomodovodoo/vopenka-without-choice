import ZFVP.Syntax.BoundedTruthTables
import ZFVP.Syntax.SigmaOneMembershipFamily

/-! Tables of truth over a set domain are determined by their constructor equations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsMembershipFormulaCode (n φ : V) : Prop := ⟨n, φ⟩ₖ ∈ (formulaFamily membershipLanguageCode ∅ : V)

instance isMembershipFormulaCode_definable : ℒₛₑₜ-relation[V] IsMembershipFormulaCode := by
  unfold IsMembershipFormulaCode
  definability

theorem IsMembershipFormulaCode.valid {n φ : V} (h : IsMembershipFormulaCode n φ) :
    φ ∈ formulaSet membershipLanguageCode ∅ n := (mem_formulaSet_iff _ _ _ _).mpr h

theorem IsMembershipFormulaCode.context {n φ : V} (h : IsMembershipFormulaCode n φ) : n ∈ (ω : V) :=
  formulaSet_context membershipLanguageCode_valid h.valid

def MembershipTruthClauses (A T n b : V) : Prop :=
  (TableHolds T n truthCode b ∧ ¬TableHolds T n falsityCode b) ∧
  (∀ r args, IsMembershipAtomicArguments n r args →
    (TableHolds T n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args) ∧
    (TableHolds T n (negAtomCode r args) b ↔ ¬DirectMembershipAtomicHolds n b r args)) ∧
  (∀ φ ψ, IsMembershipFormulaCode n φ → IsMembershipFormulaCode n ψ →
    (TableHolds T n (andCode φ ψ) b ↔ TableHolds T n φ b ∧ TableHolds T n ψ b) ∧
    (TableHolds T n (orCode φ ψ) b ↔ TableHolds T n φ b ∨ TableHolds T n ψ b)) ∧
  ∀ φ, IsMembershipFormulaCode (succ n) φ →
    (TableHolds T n (allCode φ) b ↔ ∀ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x)) ∧
    (TableHolds T n (existsCode φ) b ↔ ∃ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x))

instance membershipTruthClauses_definable : ℒₛₑₜ-relation₄[V] MembershipTruthClauses := by
  unfold MembershipTruthClauses truthCode falsityCode
  aesop (config := { terminal := true, maxRuleApplications := 1000 }) (rule_sets := [Definability])

def IsMembershipTruthTable (A T : V) : Prop := ∀ n ∈ (ω : V), ∀ b, b ∈ A ^ n → MembershipTruthClauses A T n b

instance isMembershipTruthTable_definable : ℒₛₑₜ-relation[V] IsMembershipTruthTable := by
  unfold IsMembershipTruthTable
  definability

theorem membershipTruthTables_agree {A T S : V} 
    (hT : IsMembershipTruthTable A T) (hS : IsMembershipTruthTable A S) :
    ∀ q ∈ (formulaFamily membershipLanguageCode ∅ : V), ∀ b, b ∈ A ^ (kpair.π₁ q) →
      (TableHolds T (kpair.π₁ q) (kpair.π₂ q) b ↔ TableHolds S (kpair.π₁ q) (kpair.π₂ q) b) := by
  refine formulaFamily_induction membershipLanguageCode_valid ∅
    (fun q : V ↦ ∀ b, b ∈ A ^ (kpair.π₁ q) →
      (TableHolds T (kpair.π₁ q) (kpair.π₂ q) b ↔ TableHolds S (kpair.π₁ q) (kpair.π₂ q) b))
    (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨fun b hb ↦ iff_of_true (hT n hn b hb).1.1 (hS n hn b hb).1.1,
      fun b hb ↦ iff_of_false (hT n hn b hb).1.2 (hS n hn b hb).1.2⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨fun b hb ↦ ((hT n hn b hb).2.1 r args ha').1.trans ((hS n hn b hb).2.1 r args ha').1.symm,
      fun b hb ↦ ((hT n hn b hb).2.1 r args ha').2.trans ((hS n hn b hb).2.1 r args ha').2.symm⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ihφ ihψ ⊢
    constructor <;> intro b hb
    · rw [((hT n hn b hb).2.2.1 φ ψ hφ hψ).1, ((hS n hn b hb).2.2.1 φ ψ hφ hψ).1]
      exact and_congr (ihφ b hb) (ihψ b hb)
    · rw [((hT n hn b hb).2.2.1 φ ψ hφ hψ).2, ((hS n hn b hb).2.2.1 φ ψ hφ hψ).2]
      exact or_congr (ihφ b hb) (ihψ b hb)
  · intro n hn φ hφ ih
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ih ⊢
    constructor <;> intro b hb
    · rw [((hT n hn b hb).2.2.2 φ hφ).1, ((hS n hn b hb).2.2.2 φ hφ).1]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb hx)
    · rw [((hT n hn b hb).2.2.2 φ hφ).2, ((hS n hn b hb).2.2.2 φ hφ).2]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb hx)

noncomputable def membershipModelTruthTable (A : V) : V :=
  {p ∈ (formulaFamily membershipLanguageCode ∅ : V) ×ˢ finiteSequences A ;
    kpair.π₂ p ∈ (membershipSatisfactionGraph A) ‘ ⟨kpair.π₁ (kpair.π₁ p), kpair.π₂ (kpair.π₁ p)⟩ₖ}

theorem membershipModelTruthTable_lookup {A n φ b : V} (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ A ^ n) :
    TableHolds (membershipModelTruthTable A) n φ b ↔ MembershipSatisfies A n φ b := by
  have hbseq : b ∈ finiteSequences A := (mem_finiteSequences_iff A b).mpr ⟨n, hφ.context, hb⟩
  unfold TableHolds membershipModelTruthTable
  rw [mem_sep_iff]
  have hp : ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ (formulaFamily membershipLanguageCode ∅ : V) ×ˢ finiteSequences A :=
    mem_prod_iff.mpr ⟨⟨n, φ⟩ₖ, hφ, b, hbseq, rfl⟩
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, and_iff_right hp]
  rfl

theorem membershipModelTruthTable_correct (A : V)  :
    IsMembershipTruthTable A (membershipModelTruthTable A) := by
  intro n hn b hb
  have hc := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply (membershipModelTruthTable_lookup hc.1.1 hb).mpr
    exact (satisfies_truth membershipLanguageCode_valid hn).mpr hb'
  · intro ht
    exact not_satisfies_falsity membershipLanguageCode_valid hn ((membershipModelTruthTable_lookup hc.1.2 hb).mp ht)
  · intro r args ha
    have ha' := (membershipAtomicArguments_iff hn).mpr ha
    have hcodes := hc.2.1 r args ha'
    rw [membershipModelTruthTable_lookup hcodes.1 hb, membershipModelTruthTable_lookup hcodes.2 hb,
      directMembershipAtomicHolds_iff hn hb ha]
    exact ⟨satisfies_atom membershipLanguageCode_valid hn ha' hb', satisfies_negAtom membershipLanguageCode_valid hn ha' hb'⟩
  · intro φ ψ hφ hψ
    have hcodes := hc.2.2.1 φ ψ hφ hψ
    rw [membershipModelTruthTable_lookup hcodes.1 hb, membershipModelTruthTable_lookup hcodes.2 hb,
      membershipModelTruthTable_lookup hφ hb, membershipModelTruthTable_lookup hψ hb]
    exact ⟨satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hb',
      satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hb'⟩
  · intro φ hφ
    have hcodes := hc.2.2.2 φ hφ
    rw [membershipModelTruthTable_lookup hcodes.1 hb, membershipModelTruthTable_lookup hcodes.2 hb,
      show MembershipSatisfies A n (allCode φ) b ↔ ∀ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) from by
        simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies, membershipStructureCode_domain] using satisfies_all membershipLanguageCode_valid hn hφ.valid hb',
      show MembershipSatisfies A n (existsCode φ) b ↔ ∃ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) from by
        simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies, membershipStructureCode_domain] using satisfies_exists membershipLanguageCode_valid hn hφ.valid hb']
    constructor
    · exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (membershipModelTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb hx)).symm
    · exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (membershipModelTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb hx)).symm

theorem membershipTruthTable_correct {A T n φ b : V} 
    (hT : IsMembershipTruthTable A T) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ A ^ n) :
    TableHolds T n φ b ↔ MembershipSatisfies A n φ b := by
  have he : TableHolds T n φ b ↔ TableHolds (membershipModelTruthTable A) n φ b := by
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      membershipTruthTables_agree hT (membershipModelTruthTable_correct A) _ hφ b (by simpa using hb)
  exact he.trans (membershipModelTruthTable_lookup hφ hb)

end ZFVP
