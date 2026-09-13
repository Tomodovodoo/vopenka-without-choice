import ZFVP.Syntax.PiOneBoundedCodes

/-! Constructor equations uniquely determine the bounded syntax family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_binaryCode_left (t a b : V) : rank a ∈ rank ⟨t, ⟨a, b⟩ₖ⟩ₖ :=
  IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt a b) (rank_kpair_right_lt t ⟨a, b⟩ₖ)

theorem rank_binaryCode_right (t a b : V) : rank b ∈ rank ⟨t, ⟨a, b⟩ₖ⟩ₖ :=
  IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt a b) (rank_kpair_right_lt t ⟨a, b⟩ₖ)

theorem rank_boundedAll_body (i φ : V) : rank φ ∈ rank (boundedAllCode i φ) :=
  IsOrdinal.toIsTransitive.mem_trans (rank_binaryCode_right 5 _ φ) (rank_kpair_right_lt 6 _)

theorem rank_boundedExists_body (i φ : V) : rank φ ∈ rank (boundedExistsCode i φ) :=
  IsOrdinal.toIsTransitive.mem_trans (rank_binaryCode_right 4 _ φ) (rank_kpair_right_lt 7 _)

theorem bounded_postfixed_subset {Q : V} (hQ : ∀ q ∈ Q, BoundedDerivationStep Q q) :
    Q ⊆ (boundedFormulaFamily : V) := by
  apply projectedRank_induction Q kpair.π₂ (by definability) (fun q : V ↦ q ∈ boundedFormulaFamily) (by definability)
  intro q hq ih
  obtain ⟨n, hn, φ, rfl, h⟩ := hQ q hq
  have hc := boundedFormulaFamily_closed (V := V) n hn
  rcases h with rfl | rfl | ⟨r, args, ha, h⟩ | ⟨ψ, χ, hψ, hχ, h⟩ | ⟨i, hi, ψ, hψ, h⟩
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
    · exact (hc.2.2.2 i hi ψ
        (ih _ hψ (by simpa only [kpair.π₂_kpair] using rank_boundedAll_body i ψ))).1
    · exact (hc.2.2.2 i hi ψ
        (ih _ hψ (by simpa only [kpair.π₂_kpair] using rank_boundedExists_body i ψ))).2

theorem boundedFormulaFamily_step : ∀ q ∈ (boundedFormulaFamily : V), BoundedDerivationStep boundedFormulaFamily q := by
  refine boundedFormulaFamily_induction (BoundedDerivationStep (boundedFormulaFamily : V)) (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    exact ⟨⟨n, hn, truthCode, rfl, Or.inl rfl⟩, ⟨n, hn, falsityCode, rfl, Or.inr (Or.inl rfl)⟩⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    exact ⟨⟨n, hn, atomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inl rfl⟩))⟩,
      ⟨n, hn, negAtomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inr rfl⟩))⟩⟩
  · intro n hn φ ψ hφ hψ _ _
    exact ⟨⟨n, hn, andCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hφ, hψ, Or.inl rfl⟩)))⟩,
      ⟨n, hn, orCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hφ, hψ, Or.inr rfl⟩)))⟩⟩
  · intro n hn i hi φ hφ _
    exact ⟨⟨n, hn, boundedAllCode i φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hφ, Or.inl rfl⟩)))⟩,
      ⟨n, hn, boundedExistsCode i φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hφ, Or.inr rfl⟩)))⟩⟩

end ZFVP
