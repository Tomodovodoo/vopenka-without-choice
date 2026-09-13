import ZFVP.Syntax.BoundedFixedPoints
import ZFVP.Syntax.CodingSupportSyntax

/-! Local constructor rules and fixed-point uniqueness for Levy extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def LevyDerivationStep (p : LevyPolarity) (B S q : V) : Prop := q ∈ B ∨
  ∃ n ∈ (ω : V), ∃ φ, q = ⟨n, φ⟩ₖ ∧
    ((∃ ψ χ, ⟨n, ψ⟩ₖ ∈ S ∧ ⟨n, χ⟩ₖ ∈ S ∧ (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
      (∃ i ∈ n, ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ S ∧ (φ = boundedAllCode i ψ ∨ φ = boundedExistsCode i ψ)) ∨
      ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ S ∧ φ = levyQuantifierCode p ψ)

instance levyDerivationStep_definable (p : LevyPolarity) : ℒₛₑₜ-relation₃[V] (LevyDerivationStep p) := by
  unfold LevyDerivationStep
  definability

theorem levyDerivationStep_closed {p : LevyPolarity} {B Q q : V} (hQ : IsLevyExtensionClosed p B Q)
    (h : LevyDerivationStep p B Q q) : q ∈ Q := by
  rcases h with h | ⟨n, hn, φ, rfl, h⟩
  · exact hQ.1 q h
  · have hc := hQ.2 n hn
    rcases h with ⟨ψ, χ, hψ, hχ, h⟩ | ⟨i, hi, ψ, hψ, h⟩ | ⟨ψ, hψ, rfl⟩
    · exact h.elim (fun h ↦ h ▸ (hc.1 ψ χ hψ hχ).1) (fun h ↦ h ▸ (hc.1 ψ χ hψ hχ).2)
    · exact h.elim (fun h ↦ h ▸ (hc.2.1 i hi ψ hψ).1) (fun h ↦ h ▸ (hc.2.1 i hi ψ hψ).2)
    · exact hc.2.2 ψ hψ

theorem levyExtensionFamily_step (p : LevyPolarity) {B : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) :
    ∀ q ∈ levyExtensionFamily p B, LevyDerivationStep p B (levyExtensionFamily p B) q := by
  refine levyExtensionFamily_induction p hB (LevyDerivationStep p B (levyExtensionFamily p B)) (by definability)
    (fun _ h ↦ Or.inl h) ?_ ?_ ?_
  · intro n hn φ ψ hφ hψ _ _
    exact ⟨Or.inr ⟨n, hn, andCode φ ψ, rfl, Or.inl ⟨φ, ψ, hφ, hψ, Or.inl rfl⟩⟩,
      Or.inr ⟨n, hn, orCode φ ψ, rfl, Or.inl ⟨φ, ψ, hφ, hψ, Or.inr rfl⟩⟩⟩
  · intro n hn i hi φ hφ _
    exact ⟨Or.inr ⟨n, hn, boundedAllCode i φ, rfl, Or.inr (Or.inl ⟨i, hi, φ, hφ, Or.inl rfl⟩)⟩,
      Or.inr ⟨n, hn, boundedExistsCode i φ, rfl, Or.inr (Or.inl ⟨i, hi, φ, hφ, Or.inr rfl⟩)⟩⟩
  · intro n hn φ hφ _
    exact Or.inr ⟨n, hn, levyQuantifierCode p φ, rfl, Or.inr (Or.inr ⟨φ, hφ, rfl⟩)⟩

theorem rank_levyQuantifier_body (p : LevyPolarity) (φ : V) : rank φ ∈ rank (levyQuantifierCode p φ) := by
  cases p
  · exact rank_kpair_right_lt 7 φ
  · exact rank_kpair_right_lt 6 φ

theorem levy_postfixed_subset {p : LevyPolarity} {B Q : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) (hQ : ∀ q ∈ Q, LevyDerivationStep p B Q q) :
    Q ⊆ levyExtensionFamily p B := by
  have hc := levyExtensionFamily_closed p hB
  apply projectedRank_induction Q kpair.π₂ (by definability) (fun q : V ↦ q ∈ levyExtensionFamily p B) (by definability)
  intro q hq ih
  rcases hQ q hq with hbase | ⟨n, hn, φ, rfl, h⟩
  · exact hc.1 q hbase
  · have hc := hc.2 n hn
    rcases h with ⟨ψ, χ, hψ, hχ, h⟩ | ⟨i, hi, ψ, hψ, h⟩ | ⟨ψ, hψ, rfl⟩
    · rcases h with rfl | rfl
      · exact (hc.1 ψ χ
          (ih _ hψ (by simpa only [kpair.π₂_kpair, andCode] using rank_binaryCode_left (4 : V) ψ χ))
          (ih _ hχ (by simpa only [kpair.π₂_kpair, andCode] using rank_binaryCode_right (4 : V) ψ χ))).1
      · exact (hc.1 ψ χ
          (ih _ hψ (by simpa only [kpair.π₂_kpair, orCode] using rank_binaryCode_left (5 : V) ψ χ))
          (ih _ hχ (by simpa only [kpair.π₂_kpair, orCode] using rank_binaryCode_right (5 : V) ψ χ))).2
    · rcases h with rfl | rfl
      · exact (hc.2.1 i hi ψ
          (ih _ hψ (by simpa only [kpair.π₂_kpair] using rank_boundedAll_body i ψ))).1
      · exact (hc.2.1 i hi ψ
          (ih _ hψ (by simpa only [kpair.π₂_kpair] using rank_boundedExists_body i ψ))).2
    · exact hc.2.2 ψ (ih _ hψ (by simpa only [kpair.π₂_kpair] using rank_levyQuantifier_body p ψ))

def IsLocallyLevyClosed (p : LevyPolarity) (U B Q : V) : Prop := ∀ q ∈ U, LevyDerivationStep p B Q q → q ∈ Q

theorem levyExtensionFamily_local_minimal {p : LevyPolarity} {U B Q : V} [IsCodingSupport U]
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) (hQ : IsLocallyLevyClosed p U B Q) :
    levyExtensionFamily p B ⊆ Q := by
  have hFU : levyExtensionFamily p B ⊆ U :=
    subset_trans (levyExtensionFamily_subset p B) (membershipFormulaFamily_subset_support U)
  have hc := levyExtensionFamily_closed p hB
  refine levyExtensionFamily_induction p hB (fun q : V ↦ q ∈ Q) (by definability) ?_ ?_ ?_ ?_
  · intro q hq
    exact hQ q (hFU q (hc.1 q hq)) (Or.inl hq)
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hm := (hc.2 n hn).1 φ ψ hφ hψ
    exact ⟨hQ _ (hFU _ hm.1) (Or.inr ⟨n, hn, andCode φ ψ, rfl, Or.inl ⟨φ, ψ, ihφ, ihψ, Or.inl rfl⟩⟩),
      hQ _ (hFU _ hm.2) (Or.inr ⟨n, hn, orCode φ ψ, rfl, Or.inl ⟨φ, ψ, ihφ, ihψ, Or.inr rfl⟩⟩)⟩
  · intro n hn i hi φ hφ ih
    have hm := (hc.2 n hn).2.1 i hi φ hφ
    exact ⟨hQ _ (hFU _ hm.1) (Or.inr ⟨n, hn, boundedAllCode i φ, rfl, Or.inr (Or.inl ⟨i, hi, φ, ih, Or.inl rfl⟩)⟩),
      hQ _ (hFU _ hm.2) (Or.inr ⟨n, hn, boundedExistsCode i φ, rfl, Or.inr (Or.inl ⟨i, hi, φ, ih, Or.inr rfl⟩)⟩)⟩
  · intro n hn φ hφ ih
    exact hQ _ (hFU _ ((hc.2 n hn).2.2 φ hφ))
      (Or.inr ⟨n, hn, levyQuantifierCode p φ, rfl, Or.inr (Or.inr ⟨φ, ih, rfl⟩)⟩)

end ZFVP
