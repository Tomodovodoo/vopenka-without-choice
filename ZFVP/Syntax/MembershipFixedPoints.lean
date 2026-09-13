import ZFVP.Syntax.BoundedLevySteps

/-! Local constructor equations for the full pure membership syntax family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def MembershipDerivationStep (S q : V) : Prop := ∃ n ∈ (ω : V), ∃ φ, q = ⟨n, φ⟩ₖ ∧
  (φ = truthCode ∨ φ = falsityCode ∨
    (∃ r args, IsMembershipAtomicArguments n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
    (∃ ψ χ, ⟨n, ψ⟩ₖ ∈ S ∧ ⟨n, χ⟩ₖ ∈ S ∧ (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
    ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ S ∧ (φ = allCode ψ ∨ φ = existsCode ψ))

instance membershipDerivationStep_definable : ℒₛₑₜ-relation[V] MembershipDerivationStep := by
  unfold MembershipDerivationStep truthCode falsityCode
  definability

theorem membershipDerivationStep_closed {Q q : V} (hQ : IsFormulaClosed membershipLanguageCode ∅ Q)
    (h : MembershipDerivationStep Q q) : q ∈ Q := by
  obtain ⟨n, hn, φ, rfl, h⟩ := h
  have hc := hQ n hn
  rcases h with rfl | rfl | ⟨r, args, ha, h⟩ | ⟨ψ, χ, hψ, hχ, h⟩ | ⟨ψ, hψ, h⟩
  · exact hc.1.1
  · exact hc.1.2
  · have ha' := hc.2.1 r args ((membershipAtomicArguments_iff hn).mpr ha)
    exact h.elim (fun h ↦ h ▸ ha'.1) (fun h ↦ h ▸ ha'.2)
  · exact h.elim (fun h ↦ h ▸ (hc.2.2.1 ψ χ hψ hχ).1) (fun h ↦ h ▸ (hc.2.2.1 ψ χ hψ hχ).2)
  · exact h.elim (fun h ↦ h ▸ (hc.2.2.2 ψ hψ).1) (fun h ↦ h ▸ (hc.2.2.2 ψ hψ).2)

theorem membership_postfixed_subset {Q : V} (hQ : ∀ q ∈ Q, MembershipDerivationStep Q q) :
    Q ⊆ (formulaFamily membershipLanguageCode ∅ : V) := by
  apply projectedRank_induction Q kpair.π₂ (by definability) (fun q : V ↦ q ∈ formulaFamily membershipLanguageCode ∅) (by definability)
  intro q hq ih
  obtain ⟨n, hn, φ, rfl, h⟩ := hQ q hq
  have hc := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅ n hn
  rcases h with rfl | rfl | ⟨r, args, ha, h⟩ | ⟨ψ, χ, hψ, hχ, h⟩ | ⟨ψ, hψ, h⟩
  · exact hc.1.1
  · exact hc.1.2
  · have ha' := hc.2.1 r args ((membershipAtomicArguments_iff hn).mpr ha)
    exact h.elim (fun h ↦ h ▸ ha'.1) (fun h ↦ h ▸ ha'.2)
  · rcases h with rfl | rfl
    · exact (hc.2.2.1 ψ χ
        (ih _ hψ (by simpa only [kpair.π₂_kpair, andCode, orCode] using rank_binaryCode_left (4 : V) ψ χ))
        (ih _ hχ (by simpa only [kpair.π₂_kpair, andCode, orCode] using rank_binaryCode_right (4 : V) ψ χ))).1
    · exact (hc.2.2.1 ψ χ
        (ih _ hψ (by simpa only [kpair.π₂_kpair, andCode, orCode] using rank_binaryCode_left (5 : V) ψ χ))
        (ih _ hχ (by simpa only [kpair.π₂_kpair, andCode, orCode] using rank_binaryCode_right (5 : V) ψ χ))).2
  · rcases h with rfl | rfl
    · exact (hc.2.2.2 ψ
        (ih _ hψ (by simpa only [kpair.π₂_kpair, allCode, existsCode] using rank_kpair_right_lt (6 : V) ψ))).1
    · exact (hc.2.2.2 ψ
        (ih _ hψ (by simpa only [kpair.π₂_kpair, allCode, existsCode] using rank_kpair_right_lt (7 : V) ψ))).2

theorem membershipFormulaFamily_step : ∀ q ∈ (formulaFamily membershipLanguageCode ∅ : V), MembershipDerivationStep (formulaFamily membershipLanguageCode ∅) q := by
  refine formulaFamily_induction membershipLanguageCode_valid ∅ (MembershipDerivationStep (formulaFamily membershipLanguageCode ∅ : V)) (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    exact ⟨⟨n, hn, truthCode, rfl, Or.inl rfl⟩, ⟨n, hn, falsityCode, rfl, Or.inr (Or.inl rfl)⟩⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    exact ⟨⟨n, hn, atomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inl rfl⟩))⟩,
      ⟨n, hn, negAtomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inr rfl⟩))⟩⟩
  · intro n hn φ ψ hφ hψ _ _
    exact ⟨⟨n, hn, andCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hφ, hψ, Or.inl rfl⟩)))⟩,
      ⟨n, hn, orCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hφ, hψ, Or.inr rfl⟩)))⟩⟩
  · intro n hn φ hφ _
    exact ⟨⟨n, hn, allCode φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, hφ, Or.inl rfl⟩)))⟩,
      ⟨n, hn, existsCode φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, hφ, Or.inr rfl⟩)))⟩⟩


theorem membershipFormulaFamily_local_minimal {U Q : V} [IsCodingSupport U]
    (hQ : ∀ q ∈ U, MembershipDerivationStep Q q → q ∈ Q) :
    formulaFamily membershipLanguageCode ∅ ⊆ Q := by
  have hFU := membershipFormulaFamily_subset_support (V := V) U
  have hc := formulaFamily_closed (membershipLanguageCode_valid (V := V)) ∅
  refine formulaFamily_induction membershipLanguageCode_valid ∅ (fun q : V ↦ q ∈ Q)
    (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    exact ⟨hQ _ (hFU _ (hc n hn).1.1) ⟨n, hn, truthCode, rfl, Or.inl rfl⟩,
      hQ _ (hFU _ (hc n hn).1.2) ⟨n, hn, falsityCode, rfl, Or.inr (Or.inl rfl)⟩⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    have hm := (hc n hn).2.1 r args ha
    exact ⟨hQ _ (hFU _ hm.1) ⟨n, hn, atomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inl rfl⟩))⟩,
      hQ _ (hFU _ hm.2) ⟨n, hn, negAtomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inr rfl⟩))⟩⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hm := (hc n hn).2.2.1 φ ψ hφ hψ
    exact ⟨hQ _ (hFU _ hm.1) ⟨n, hn, andCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, ihφ, ihψ, Or.inl rfl⟩)))⟩,
      hQ _ (hFU _ hm.2) ⟨n, hn, orCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, ihφ, ihψ, Or.inr rfl⟩)))⟩⟩
  · intro n hn φ hφ ih
    have hm := (hc n hn).2.2.2 φ hφ
    exact ⟨hQ _ (hFU _ hm.1) ⟨n, hn, allCode φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, ih, Or.inl rfl⟩)))⟩,
      hQ _ (hFU _ hm.2) ⟨n, hn, existsCode φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, ih, Or.inr rfl⟩)))⟩⟩

end ZFVP
