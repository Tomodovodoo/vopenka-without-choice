import ZFVP.Syntax.DirectMembershipAtoms
import ZFVP.Syntax.BoundedSatisfaction

/-! Tables of bounded truth are determined by their constructor equations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def TableHolds (T n φ b : V) : Prop := ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ T

instance tableHolds_definable : ℒₛₑₜ-relation₄[V] TableHolds := by unfold TableHolds; definability

def BoundedTruthClauses (T n b : V) : Prop :=
  (TableHolds T n truthCode b ∧ ¬TableHolds T n falsityCode b) ∧
  (∀ r args, IsMembershipAtomicArguments n r args →
    (TableHolds T n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args) ∧
    (TableHolds T n (negAtomCode r args) b ↔ ¬DirectMembershipAtomicHolds n b r args)) ∧
  (∀ φ ψ, IsBoundedFormulaCode n φ → IsBoundedFormulaCode n ψ →
    (TableHolds T n (andCode φ ψ) b ↔ TableHolds T n φ b ∧ TableHolds T n ψ b) ∧
    (TableHolds T n (orCode φ ψ) b ↔ TableHolds T n φ b ∨ TableHolds T n ψ b)) ∧
  ∀ i ∈ n, ∀ φ, IsBoundedFormulaCode (succ n) φ →
    (TableHolds T n (boundedAllCode i φ) b ↔ ∀ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x)) ∧
    (TableHolds T n (boundedExistsCode i φ) b ↔ ∃ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x))

instance boundedTruthClauses_definable : ℒₛₑₜ-relation₃[V] BoundedTruthClauses := by
  unfold BoundedTruthClauses truthCode falsityCode
  aesop (config := { terminal := true, maxRuleApplications := 1000 }) (rule_sets := [Definability])

def IsBoundedTruthTable (A T : V) : Prop := ∀ n ∈ (ω : V), ∀ b, b ∈ A ^ n → BoundedTruthClauses T n b

instance isBoundedTruthTable_definable : ℒₛₑₜ-relation[V] IsBoundedTruthTable := by
  unfold IsBoundedTruthTable
  definability

theorem boundedTruthTables_agree {A T S : V} [hA : IsTransitive A]
    (hT : IsBoundedTruthTable A T) (hS : IsBoundedTruthTable A S) :
    ∀ q ∈ (boundedFormulaFamily : V), ∀ b, b ∈ A ^ (kpair.π₁ q) →
      (TableHolds T (kpair.π₁ q) (kpair.π₂ q) b ↔ TableHolds S (kpair.π₁ q) (kpair.π₂ q) b) := by
  refine boundedFormulaFamily_induction
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
  · intro n hn i hi φ hφ ih
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ih ⊢
    constructor <;> intro b hb
    · rw [((hT n hn b hb).2.2.2 i hi φ hφ).1, ((hS n hn b hb).2.2.2 i hi φ hφ).1]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb (hA.mem_trans hx (function_value_mem hb hi)))
    · rw [((hT n hn b hb).2.2.2 i hi φ hφ).2, ((hS n hn b hb).2.2.2 i hi φ hφ).2]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb (hA.mem_trans hx (function_value_mem hb hi)))

noncomputable def boundedModelTruthTable (A : V) : V :=
  {p ∈ (boundedFormulaFamily : V) ×ˢ finiteSequences A ;
    kpair.π₂ p ∈ (membershipSatisfactionGraph A) ‘ ⟨kpair.π₁ (kpair.π₁ p), kpair.π₂ (kpair.π₁ p)⟩ₖ}

theorem boundedModelTruthTable_lookup {A n φ b : V} (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ A ^ n) :
    TableHolds (boundedModelTruthTable A) n φ b ↔ MembershipSatisfies A n φ b := by
  have hbseq : b ∈ finiteSequences A := (mem_finiteSequences_iff A b).mpr ⟨n, hφ.context, hb⟩
  unfold TableHolds boundedModelTruthTable
  rw [mem_sep_iff]
  have hp : ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ (boundedFormulaFamily : V) ×ˢ finiteSequences A :=
    mem_prod_iff.mpr ⟨⟨n, φ⟩ₖ, hφ, b, hbseq, rfl⟩
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, and_iff_right hp]
  rfl

theorem boundedModelTruthTable_correct (A : V) [hA : IsTransitive A] :
    IsBoundedTruthTable A (boundedModelTruthTable A) := by
  intro n hn b hb
  have hc := boundedFormulaFamily_closed (V := V) n hn
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply (boundedModelTruthTable_lookup hc.1.1 hb).mpr
    exact (satisfies_truth membershipLanguageCode_valid hn).mpr hb'
  · intro ht
    exact not_satisfies_falsity membershipLanguageCode_valid hn ((boundedModelTruthTable_lookup hc.1.2 hb).mp ht)
  · intro r args ha
    have ha' := (membershipAtomicArguments_iff hn).mpr ha
    have hcodes := hc.2.1 r args ha'
    rw [boundedModelTruthTable_lookup hcodes.1 hb, boundedModelTruthTable_lookup hcodes.2 hb,
      directMembershipAtomicHolds_iff hn hb ha]
    exact ⟨satisfies_atom membershipLanguageCode_valid hn ha' hb', satisfies_negAtom membershipLanguageCode_valid hn ha' hb'⟩
  · intro φ ψ hφ hψ
    have hcodes := hc.2.2.1 φ ψ hφ hψ
    rw [boundedModelTruthTable_lookup hcodes.1 hb, boundedModelTruthTable_lookup hcodes.2 hb,
      boundedModelTruthTable_lookup hφ hb, boundedModelTruthTable_lookup hψ hb]
    exact ⟨satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hb',
      satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hb'⟩
  · intro i hi φ hφ
    have hcodes := hc.2.2.2 i hi φ hφ
    rw [boundedModelTruthTable_lookup hcodes.1 hb, boundedModelTruthTable_lookup hcodes.2 hb,
      membershipSatisfies_boundedAll hn hi hφ.valid hb, membershipSatisfies_boundedExists hn hi hφ.valid hb]
    constructor
    · exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (boundedModelTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb (hA.mem_trans hx (function_value_mem hb hi)))).symm
    · exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (boundedModelTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb (hA.mem_trans hx (function_value_mem hb hi)))).symm

theorem boundedTruthTable_correct {A T n φ b : V} [IsTransitive A]
    (hT : IsBoundedTruthTable A T) (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ A ^ n) :
    TableHolds T n φ b ↔ MembershipSatisfies A n φ b := by
  have he : TableHolds T n φ b ↔ TableHolds (boundedModelTruthTable A) n φ b := by
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      boundedTruthTables_agree hT (boundedModelTruthTable_correct A) _ hφ b (by simpa using hb)
  exact he.trans (boundedModelTruthTable_lookup hφ hb)

end ZFVP
