import ZFVP.Syntax.EndExtensionMembershipPreimages

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An external property can use internal induction when represented by a definable target predicate. -/
theorem membershipFormula_induction_via (j : MembershipEndExtension V W)
    (P : V → V → Prop) (Q : W → Prop) (hQ : ℒₛₑₜ-predicate Q)
    (bridge : ∀ n φ, IsMembershipFormulaCode n φ → (Q (j ⟨n, φ⟩ₖ) ↔ P n φ))
    (hc : ∀ n ∈ (ω : V), P n truthCode ∧ P n falsityCode)
    (ha : ∀ n ∈ (ω : V), ∀ r args, IsAtomicArguments membershipLanguageCode ∅ n r args →
      P n (atomCode r args) ∧ P n (negAtomCode r args))
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, IsMembershipFormulaCode n φ → IsMembershipFormulaCode n ψ →
      P n φ → P n ψ → P n (andCode φ ψ) ∧ P n (orCode φ ψ))
    (hq : ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ n) φ →
      P (succ n) φ → P n (allCode φ) ∧ P n (existsCode φ)) :
    ∀ n φ, IsMembershipFormulaCode n φ → P n φ := by
  have hmain : ∀ q ∈ (formulaFamily membershipLanguageCode ∅ : W), Q q := by
    apply formulaFamily_induction membershipLanguageCode_valid ∅ Q hQ
    · intro m hm
      rw [← j.map_omega] at hm
      obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
      have hf := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn
      constructor
      · rw [← j.map_truthCode, ← j.map_kpair]
        exact (bridge n truthCode hf.1.1).mpr (hc n hn).1
      · rw [← j.map_falsityCode, ← j.map_kpair]
        exact (bridge n falsityCode hf.1.2).mpr (hc n hn).2
    · intro m hm r args hargs
      rw [← j.map_omega] at hm
      obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
      obtain ⟨s, bs, rfl, rfl, hs⟩ := j.membershipAtomic_preimages hn hargs
      have hf := (formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn).2.1 s bs hs
      constructor
      · rw [← j.map_atomCode, ← j.map_kpair]
        exact (bridge n _ hf.1).mpr (ha n hn s bs hs).1
      · rw [← j.map_negAtomCode, ← j.map_kpair]
        exact (bridge n _ hf.2).mpr (ha n hn s bs hs).2
    · intro m hm φ ψ hφ hψ ihφ ihψ
      rw [← j.map_omega] at hm
      obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
      obtain ⟨a, rfl, ha'⟩ := j.membershipFormulaCode_preimage_at hφ
      obtain ⟨b, rfl, hb'⟩ := j.membershipFormulaCode_preimage_at hψ
      rw [← j.map_kpair] at ihφ ihψ
      have hh := hb n hn a b ha' hb' ((bridge n a ha').mp ihφ) ((bridge n b hb').mp ihψ)
      have hf := (formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn).2.2.1 a b ha' hb'
      constructor
      · rw [← j.map_andCode, ← j.map_kpair]
        exact (bridge n _ hf.1).mpr hh.1
      · rw [← j.map_orCode, ← j.map_kpair]
        exact (bridge n _ hf.2).mpr hh.2
    · intro m hm φ hφ ihφ
      rw [← j.map_omega] at hm
      obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
      rw [← j.map_succ] at hφ ihφ
      obtain ⟨a, rfl, ha'⟩ := j.membershipFormulaCode_preimage_at hφ
      rw [← j.map_kpair] at ihφ
      have hh := hq n hn a ha' ((bridge (succ n) a ha').mp ihφ)
      have hf := (formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn).2.2.2 a ha'
      constructor
      · rw [← j.map_allCode, ← j.map_kpair]
        exact (bridge n _ hf.1).mpr hh.1
      · rw [← j.map_existsCode, ← j.map_kpair]
        exact (bridge n _ hf.2).mpr hh.2
  intro n φ hφ
  apply (bridge n φ hφ).mp
  apply hmain
  rw [← j.map_membershipFormulaFamily, j.mem_iff]
  exact hφ

end MembershipEndExtension
end ZFVP
