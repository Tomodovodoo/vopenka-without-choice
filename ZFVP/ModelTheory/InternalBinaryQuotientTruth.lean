import ZFVP.ModelTheory.InternalBinaryQuotientAtoms
import ZFVP.Syntax.MembershipTruthTables
import ZFVP.Syntax.UniformSatisfaction
import ZFVP.ModelTheory.CodedZFModel

/-! An actual truth table on names descends through its internal equality
quotient. The induction covers every internally finite formula code. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def NameTruthClauses (D E R T n b : V) : Prop :=
  (TableHolds T n truthCode b ∧ ¬TableHolds T n falsityCode b) ∧
  (∀ r args, IsMembershipAtomicArguments n r args →
    (TableHolds T n (atomCode r args) b ↔ DirectNameAtomicHolds E R n b r args) ∧
    (TableHolds T n (negAtomCode r args) b ↔ ¬DirectNameAtomicHolds E R n b r args)) ∧
  (∀ φ ψ, IsMembershipFormulaCode n φ → IsMembershipFormulaCode n ψ →
    (TableHolds T n (andCode φ ψ) b ↔ TableHolds T n φ b ∧ TableHolds T n ψ b) ∧
    (TableHolds T n (orCode φ ψ) b ↔ TableHolds T n φ b ∨ TableHolds T n ψ b)) ∧
  ∀ φ, IsMembershipFormulaCode (succ n) φ →
    (TableHolds T n (allCode φ) b ↔ ∀ x ∈ D, TableHolds T (succ n) φ (assignmentPrepend n b x)) ∧
    (TableHolds T n (existsCode φ) b ↔ ∃ x ∈ D, TableHolds T (succ n) φ (assignmentPrepend n b x))

def IsNameTruthTable (D E R T : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ b, b ∈ D ^ n → NameTruthClauses D E R T n b

instance isNameTruthTable_definable : ℒₛₑₜ-relation₄[V] IsNameTruthTable := by
  unfold IsNameTruthTable NameTruthClauses DirectNameAtomicHolds truthCode falsityCode
  aesop (config := { terminal := true, maxRuleApplications := 2500 }) (rule_sets := [Definability])

theorem nameTruthTable_quotient {D E R T : V} (hE : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) (hT : IsNameTruthTable D E R T) :
    ∀ n φ, φ ∈ formulaSet membershipLanguageCode ∅ n → ∀ b, b ∈ D ^ n →
      (TableHolds T n φ b ↔ Satisfies membershipLanguageCode ∅
        (internalQuotientStructure D E R) ∅ n φ (compose b (internalQuotientProjection D E))) := by
  let M := internalQuotientStructure D E R
  let q := internalQuotientProjection D E
  have hq {n b : V} (hb : b ∈ D ^ n) : compose b q ∈ structureDomain M ^ n := by
    simpa only [M, internalQuotientStructure_domain] using quotientAssignment_mem hb
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  refine formulaSet_induction membershipLanguageCode_valid ∅
    (fun n φ : V ↦ ∀ b, b ∈ D ^ n →
      (TableHolds T n φ b ↔ Satisfies membershipLanguageCode ∅ M ∅ n φ (compose b q)))
    (by unfold TableHolds Satisfies; definability) ?_ ?_ ?_ ?_
  · intro n hn
    constructor
    · intro b hb
      exact iff_of_true (hT n hn b hb).1.1 ((satisfies_truth membershipLanguageCode_valid hn).mpr (hq hb))
    · intro b hb
      exact iff_of_false (hT n hn b hb).1.2 (not_satisfies_falsity membershipLanguageCode_valid hn)
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    constructor
    · intro b hb
      rw [((hT n hn b hb).2.1 r args ha').1,
        satisfies_atom membershipLanguageCode_valid hn ha (hq hb)]
      exact directNameAtomicHolds_quotient hE hR hn hb ha'
    · intro b hb
      rw [((hT n hn b hb).2.1 r args ha').2,
        satisfies_negAtom membershipLanguageCode_valid hn ha (hq hb)]
      exact not_congr (directNameAtomicHolds_quotient hE hR hn hb ha')
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hφ' : IsMembershipFormulaCode n φ := (mem_formulaSet_iff _ _ _ _).mp hφ
    have hψ' : IsMembershipFormulaCode n ψ := (mem_formulaSet_iff _ _ _ _).mp hψ
    constructor <;> intro b hb
    · rw [((hT n hn b hb).2.2.1 φ ψ hφ' hψ').1,
        satisfies_and membershipLanguageCode_valid hn hφ hψ (hq hb)]
      exact and_congr (ihφ b hb) (ihψ b hb)
    · rw [((hT n hn b hb).2.2.1 φ ψ hφ' hψ').2,
        satisfies_or membershipLanguageCode_valid hn hφ hψ (hq hb)]
      exact or_congr (ihφ b hb) (ihψ b hb)
  · intro n hn φ hφ ih
    have hφ' : IsMembershipFormulaCode (succ n) φ := (mem_formulaSet_iff _ _ _ _).mp hφ
    have hxq {x : V} (hx : x ∈ D) : internalEquivalenceClass D E x ∈ structureDomain M := by
      simp only [M, internalQuotientStructure_domain]
      exact (mem_internalQuotientCarrier _ _ _).mpr ⟨x, hx, rfl⟩
    have heq {b x : V} (hb : b ∈ D ^ n) (hx : x ∈ D) :
        TableHolds T (succ n) φ (assignmentPrepend n b x) ↔
          Satisfies membershipLanguageCode ∅ M ∅ (succ n) φ
            (assignmentPrepend n (compose b q) (internalEquivalenceClass D E x)) := by
      rw [← quotientAssignment_prepend hn hb hx]
      exact ih _ (assignmentPrepend_mem_function hn hb hx)
    constructor <;> intro b hb
    · rw [((hT n hn b hb).2.2.2 φ hφ').1,
        satisfies_all membershipLanguageCode_valid hn hφ (hq hb)]
      constructor
      · intro hh y hy
        have hy' : y ∈ internalQuotientCarrier D E := by simpa only [M, internalQuotientStructure_domain] using hy
        obtain ⟨x, hx, rfl⟩ := (mem_internalQuotientCarrier D E y).mp hy'
        exact (heq hb hx).mp (hh x hx)
      · intro hh x hx
        exact (heq hb hx).mpr (hh _ (hxq hx))
    · rw [((hT n hn b hb).2.2.2 φ hφ').2,
        satisfies_exists membershipLanguageCode_valid hn hφ (hq hb)]
      constructor
      · rintro ⟨x, hx, hh⟩
        exact ⟨_, hxq hx, (heq hb hx).mp hh⟩
      · rintro ⟨y, hy, hh⟩
        have hy' : y ∈ internalQuotientCarrier D E := by simpa only [M, internalQuotientStructure_domain] using hy
        obtain ⟨x, hx, rfl⟩ := (mem_internalQuotientCarrier D E y).mp hy'
        exact ⟨x, hx, (heq hb hx).mpr hh⟩

theorem nameTruthTable_sentence_quotient {D E R T φ : V} (hE : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) (hT : IsNameTruthTable D E R T)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (0 : V)) :
    TableHolds T 0 φ ∅ ↔ Satisfies membershipLanguageCode ∅ (internalQuotientStructure D E R) ∅ 0 φ ∅ := by
  simpa only [graph_empty_compose] using nameTruthTable_quotient hE hR hT 0 φ hφ ∅
    (by simp [mem_function_iff, zero_def])

theorem nameTruthTable_quotient_codedZF {D E R T : V} (hD : IsNonempty D)
    (hE : IsInternalSetoid D E) (hR : IsInternalRelationCongruence D E R)
    (hT : IsNameTruthTable D E R T)
    (hzf : ∀ φ ∈ (zfClosedAxiomCodes : V), TableHolds T 0 φ ∅) :
    IsCodedZFModel (internalQuotientStructure D E R) := by
  apply (isCodedZFModel_iff_closed _).mpr
  refine ⟨internalQuotientStructure_valid hD, fun φ hφ ↦ ?_⟩
  exact (nameTruthTable_sentence_quotient hE hR hT (zfClosedAxiomCodes_valid hφ)).mp (hzf φ hφ)

end ZFVP
