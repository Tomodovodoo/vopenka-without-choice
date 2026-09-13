import ZFVP.Syntax.InternalForcingEquations
import ZFVP.Syntax.MembershipTruthTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcingTableHolds (T n φ b p : V) : Prop := ⟨⟨n, φ⟩ₖ, ⟨b, p⟩ₖ⟩ₖ ∈ T

instance forcingTableHolds_definable : ℒₛₑₜ-relation₅[V] ForcingTableHolds := by
  unfold ForcingTableHolds
  definability

instance internalForces_definable (P R D : V) : ℒₛₑₜ-relation₄ (InternalForces P R D) := by
  unfold InternalForces
  definability

def InternalForcingTruthClauses (P R D T n b p : V) : Prop :=
  (ForcingTableHolds T n truthCode b p ∧ ¬ForcingTableHolds T n falsityCode b p) ∧
  (∀ r args, IsMembershipAtomicArguments n r args →
    (ForcingTableHolds T n (atomCode r args) b p ↔ InternalForcingAtomicHolds P R n b r args p) ∧
    (ForcingTableHolds T n (negAtomCode r args) b p ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬InternalForcingAtomicHolds P R n b r args q)) ∧
  (∀ φ ψ, IsMembershipFormulaCode n φ → IsMembershipFormulaCode n ψ →
    (ForcingTableHolds T n (andCode φ ψ) b p ↔ ForcingTableHolds T n φ b p ∧ ForcingTableHolds T n ψ b p) ∧
    (ForcingTableHolds T n (orCode φ ψ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ (ForcingTableHolds T n φ b r ∨ ForcingTableHolds T n ψ b r))) ∧
  ∀ φ, IsMembershipFormulaCode (succ n) φ →
    (ForcingTableHolds T n (allCode φ) b p ↔
      ∀ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) p) ∧
    (ForcingTableHolds T n (existsCode φ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) r)

instance internalForcingTruthClauses_definable (P R D : V) :
    ℒₛₑₜ-relation₄ (InternalForcingTruthClauses P R D) := by
  unfold InternalForcingTruthClauses truthCode falsityCode
  repeat' first | apply Language.Definable.and | (solve | definability)

def IsInternalForcingTruthTable (P R D T : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ b, b ∈ D ^ n → ∀ p ∈ P, InternalForcingTruthClauses P R D T n b p

instance isInternalForcingTruthTable_definable (P R D : V) :
    ℒₛₑₜ-predicate (IsInternalForcingTruthTable P R D) := by
  unfold IsInternalForcingTruthTable
  definability

noncomputable def internalForcingTruthTable (P R D : V) : V :=
  {z ∈ (formulaFamily membershipLanguageCode ∅ : V) ×ˢ (finiteSequences D ×ˢ P) ;
    kpair.π₂ z ∈ (internalForcingGraph P R D) ‘ (kpair.π₁ z)}

theorem internalForcingTruthTable_lookup {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    ForcingTableHolds (internalForcingTruthTable P R D) n φ b p ↔ InternalForces P R D n φ b p := by
  have hseq : b ∈ finiteSequences D := (mem_finiteSequences_iff D b).mpr ⟨n, hφ.context, hb⟩
  unfold ForcingTableHolds internalForcingTruthTable InternalForces
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  exact and_iff_right ⟨hφ, hseq, hp⟩

theorem internalForcingTruthTable_correct (P R D : V) :
    IsInternalForcingTruthTable P R D (internalForcingTruthTable P R D) := by
  intro n hn b hb p hp
  have hc := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (internalForcingTruthTable_lookup hc.1.1 hb hp).mpr ((internalForces_truth hn).mpr ⟨hb, hp⟩)
  · intro ht
    exact not_internalForces_falsity hn ((internalForcingTruthTable_lookup hc.1.2 hb hp).mp ht)
  · intro r args ha
    have ha' := (membershipAtomicArguments_iff hn).mpr ha
    exact ⟨(internalForcingTruthTable_lookup (hc.2.1 r args ha').1 hb hp).trans
        (internalForces_atom hn ha' hb hp),
      (internalForcingTruthTable_lookup (hc.2.1 r args ha').2 hb hp).trans
        (internalForces_negAtom hn ha' hb hp)⟩
  · intro φ ψ hφ hψ
    constructor
    · rw [internalForcingTruthTable_lookup (hc.2.2.1 φ ψ hφ hψ).1 hb hp,
        internalForces_and hn hφ.valid hψ.valid hb hp,
        internalForcingTruthTable_lookup hφ hb hp, internalForcingTruthTable_lookup hψ hb hp]
    · rw [internalForcingTruthTable_lookup (hc.2.2.1 φ ψ hφ hψ).2 hb hp,
        internalForces_or hn hφ.valid hψ.valid hb hp]
      apply forall_congr'
      intro q
      apply imp_congr_right
      intro _
      apply imp_congr_right
      intro _
      apply exists_congr
      intro r
      apply and_congr_right
      intro hr
      exact and_congr Iff.rfl ((internalForcingTruthTable_lookup hφ hb hr).or
        (internalForcingTruthTable_lookup hψ hb hr)).symm
  · intro φ hφ
    constructor
    · rw [internalForcingTruthTable_lookup (hc.2.2.2 φ hφ).1 hb hp,
        internalForces_all hn hφ.valid hb hp]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (internalForcingTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb hx) hp).symm
    · rw [internalForcingTruthTable_lookup (hc.2.2.2 φ hφ).2 hb hp,
        internalForces_exists hn hφ.valid hb hp]
      apply forall_congr'
      intro q
      apply imp_congr_right
      intro _
      apply imp_congr_right
      intro _
      apply exists_congr
      intro r
      apply and_congr_right
      intro hr
      apply and_congr Iff.rfl
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (internalForcingTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb hx) hr).symm

end ZFVP
