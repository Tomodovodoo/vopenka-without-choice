import ZFVP.Syntax.InternalForcingSets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalForcingSet_all {P R D n b φ : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (allCode φ) b = forcingClassIntersection P (fun x ↦ x ∈ D) (by definability)
      (fun x ↦ internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) (by definability) := by
  apply mem_ext
  intro p
  rw [mem_internalForcingSet_raw, mem_forcingClassIntersection_iff]
  apply and_congr_right
  intro hp
  rw [internalForces_all hn hφ.valid hb hp]
  simp only [mem_internalForcingSet hφ]

theorem internalForcingSet_exists {P R D n b φ : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (existsCode φ) b = forcingExistential P R (fun x ↦ x ∈ D) (by definability)
      (fun x ↦ internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) (by definability) := by
  apply mem_ext
  intro p
  rw [mem_internalForcingSet_raw, forcingExistential, mem_forcingClosure_iff]
  apply and_congr_right
  intro hp
  rw [internalForces_exists hn hφ.valid hb hp]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  simp only [mem_forcingClassUnion_iff, mem_internalForcingSet hφ]
  constructor
  · rintro ⟨r, hr, hrq, hx⟩
    exact ⟨r, ⟨hr, hx⟩, hrq⟩
  · rintro ⟨r, ⟨hr, hx⟩, hrq⟩
    exact ⟨r, hr, hrq, hx⟩

theorem internalForcingSet_regular {P R D n φ b : V} (hR : IsForcingPreorder P R)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) :
    IsForcingRegular P R (internalForcingSet P R D n φ b) := by
  have hall : ∀ n : V, ∀ φ ∈ formulaSet membershipLanguageCode ∅ n, ∀ b ∈ D ^ n,
      IsForcingRegular P R (internalForcingSet P R D n φ b) := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ b ∈ D ^ n, IsForcingRegular P R (internalForcingSet P R D n φ b))
      (by definability) ?_ ?_ ?_ ?_
    · intro n hn
      constructor <;> intro b hb
      · rw [internalForcingSet_truth (P := P) (R := R) hn hb]
        exact forcingRegular_top P R
      · rw [internalForcingSet_falsity (P := P) (R := R) (D := D) (b := b) hn]
        exact forcingRegular_empty hR
    · intro n hn r args ha
      constructor <;> intro b hb
      · rw [internalForcingSet_atom hn ha hb]
        exact internalAtomicForcingSet_regular hR ((membershipAtomicArguments_iff hn).mp ha)
      · rw [internalForcingSet_negAtom hn ha hb]
        exact forcingNegation_regular hR (internalAtomicForcingSet_regular hR ((membershipAtomicArguments_iff hn).mp ha)).2.1
    · intro n hn φ ψ hφ hψ ihφ ihψ
      have hφ := (mem_formulaSet_iff _ _ _ _).mp hφ
      have hψ := (mem_formulaSet_iff _ _ _ _).mp hψ
      constructor <;> intro b hb
      · rw [internalForcingSet_and hφ hψ hb]
        exact forcingRegular_inter (ihφ b hb) (ihψ b hb)
      · rw [internalForcingSet_or hφ hψ hb]
        apply forcingClosure_regular hR
        intro p hp
        exact (mem_union_iff.mp hp).elim ((ihφ b hb).1 p) ((ihψ b hb).1 p)
    · intro n hn φ hφ ih
      have hφ := (mem_formulaSet_iff _ _ _ _).mp hφ
      constructor <;> intro b hb
      · rw [internalForcingSet_all hn hφ hb]
        apply forcingClassIntersection_regular
        intro x hx
        exact ih _ (assignmentPrepend_mem_function hn hb hx)
      · rw [internalForcingSet_exists hn hφ hb]
        exact forcingExistential_regular hR _ _ _ _
  exact hall n φ hφ.valid b hb

end ZFVP
