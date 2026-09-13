import ZFVP.Syntax.InternalForcingTruthTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem dense_congr (P R p : V) {F G : V → Prop} (h : ∀ r ∈ P, F r ↔ G r) :
    (∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ F r) ↔
      (∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ G r) := by
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  exact exists_congr fun r ↦ and_congr_right fun hr ↦ and_congr Iff.rfl (h r hr)

theorem internalForcingTruthTables_agree {P R D T S : V}
    (hT : IsInternalForcingTruthTable P R D T) (hS : IsInternalForcingTruthTable P R D S) :
    ∀ q ∈ (formulaFamily membershipLanguageCode ∅ : V), ∀ b, b ∈ D ^ (kpair.π₁ q) → ∀ p ∈ P,
      (ForcingTableHolds T (kpair.π₁ q) (kpair.π₂ q) b p ↔
        ForcingTableHolds S (kpair.π₁ q) (kpair.π₂ q) b p) := by
  refine formulaFamily_induction membershipLanguageCode_valid ∅
    (fun q : V ↦ ∀ b, b ∈ D ^ (kpair.π₁ q) → ∀ p ∈ P,
      (ForcingTableHolds T (kpair.π₁ q) (kpair.π₂ q) b p ↔
        ForcingTableHolds S (kpair.π₁ q) (kpair.π₂ q) b p))
    (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨fun b hb p hp ↦ iff_of_true (hT n hn b hb p hp).1.1 (hS n hn b hb p hp).1.1,
      fun b hb p hp ↦ iff_of_false (hT n hn b hb p hp).1.2 (hS n hn b hb p hp).1.2⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨fun b hb p hp ↦ ((hT n hn b hb p hp).2.1 r args ha').1.trans
        ((hS n hn b hb p hp).2.1 r args ha').1.symm,
      fun b hb p hp ↦ ((hT n hn b hb p hp).2.1 r args ha').2.trans
        ((hS n hn b hb p hp).2.1 r args ha').2.symm⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ihφ ihψ ⊢
    constructor <;> intro b hb p hp
    · rw [((hT n hn b hb p hp).2.2.1 φ ψ hφ hψ).1,
        ((hS n hn b hb p hp).2.2.1 φ ψ hφ hψ).1]
      exact and_congr (ihφ b hb p hp) (ihψ b hb p hp)
    · rw [((hT n hn b hb p hp).2.2.1 φ ψ hφ hψ).2,
        ((hS n hn b hb p hp).2.2.1 φ ψ hφ hψ).2]
      exact dense_congr P R p (fun r hr ↦ or_congr (ihφ b hb r hr) (ihψ b hb r hr))
  · intro n hn φ hφ ih
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at ih ⊢
    constructor <;> intro b hb p hp
    · rw [((hT n hn b hb p hp).2.2.2 φ hφ).1, ((hS n hn b hb p hp).2.2.2 φ hφ).1]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb hx) p hp
    · rw [((hT n hn b hb p hp).2.2.2 φ hφ).2, ((hS n hn b hb p hp).2.2.2 φ hφ).2]
      exact dense_congr P R p (fun r hr ↦ exists_congr fun x ↦ and_congr_right fun hx ↦
        ih _ (assignmentPrepend_mem_function hn hb hx) r hr)

theorem IsInternalForcingTruthTable.lookup {P R D T n φ b p : V}
    (hT : IsInternalForcingTruthTable P R D T) (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ D ^ n) (hp : p ∈ P) : ForcingTableHolds T n φ b p ↔ InternalForces P R D n φ b p := by
  have he := internalForcingTruthTables_agree hT (internalForcingTruthTable_correct P R D) ⟨n, φ⟩ₖ hφ
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
  exact (he b hb p hp).trans (internalForcingTruthTable_lookup hφ hb hp)

end ZFVP
