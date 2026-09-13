import ZFVP.ModelTheory.SchmerlInternalDeduction

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalDerivationCode.fragment_data {L Γ n φ c : V}
    (h : IsInternalDerivationCode L Γ n φ c) :
    ∃ F, IsFragment L F ∧ IsInternallyCountable F ∧ Γ ⊆ F ∧ ⟨n, φ⟩ₖ ∈ F := by
  obtain ⟨F, D, d, _, hFc, _, hP, hd, hl⟩ := h
  exact ⟨F, hP.1, hFc, hP.2.1, by simpa only [hl] using (hP.2.2 d hd).label_mem⟩

/-- The classical axiom, applied to an actual derivation of its antecedent. -/
theorem IsInternalDerivationCode.classical_contrapose {L Γ n φ ψ c : V}
    (h : IsInternalDerivationCode L Γ n (impCode (negCode φ) (negCode ψ)) c) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode ψ φ) z := by
  obtain ⟨F, hF, hFc, hΓF, hp⟩ := h.fragment_data
  have hφ := hF.neg_mem (hF.imp_left_mem hp)
  have hψ := hF.neg_mem (hF.imp_right_mem hp)
  have hA := impFragment_valid hF hψ hφ
  have hAc := impFragment_countable (n := n) (φ := ψ) (ψ := φ) hFc
  have hFA := impFragment_subset F n ψ φ
  have hB := impFragment_valid hA (hFA _ hp) (impFragment_mem F n ψ φ)
  obtain ⟨a, ha⟩ := internalDerivation_boolean hB (impFragment_countable hAc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hFA t (hΓF t ht)))
    (impFragment_mem _ _ _ _) (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, rfl⟩))))
  exact ha.mp h

/-- Contradictory actual derivations yield every formula in a supplied fragment. -/
theorem IsInternalDerivationCode.explode {L Γ H n φ ψ c e : V}
    (h : IsInternalDerivationCode L Γ n φ c)
    (k : IsInternalDerivationCode L Γ n (negCode φ) e)
    (hH : IsFragment L H) (hHc : IsInternallyCountable H) (hψ : ⟨n, ψ⟩ₖ ∈ H) :
    ∃ z, IsInternalDerivationCode L Γ n ψ z := by
  obtain ⟨a, ha⟩ := k.weaken_imp (ψ := negCode ψ) (hH.insert_neg hψ)
    (internallyCountable_insert hHc ⟨n, negCode ψ⟩ₖ) (by simp)
  obtain ⟨b, hb⟩ := ha.classical_contrapose
  exact hb.mp h

/-- Reductio discharges a negative sentence from two contradictory derivations. -/
theorem internalDerivation_reductio {L Γ F χ ψ c e : V}
    (hF : IsFragment L F) (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hχ : ⟨(0 : V), χ⟩ₖ ∈ F) (hAC : InternalChoice V)
    (h : IsInternalDerivationCode L (insert ⟨(0 : V), negCode χ⟩ₖ Γ) 0 ψ c)
    (k : IsInternalDerivationCode L (insert ⟨(0 : V), negCode χ⟩ₖ Γ) 0 (negCode ψ) e) :
    ∃ z, IsInternalDerivationCode L Γ 0 χ z := by
  let A := insert ⟨(0 : V), negCode χ⟩ₖ F
  have hA : IsFragment L A := hF.insert_neg hχ
  have hAc : IsInternallyCountable A := internallyCountable_insert hFc _
  have hneg : ⟨(0 : V), negCode χ⟩ₖ ∈ A := by simp [A]
  let T := impCode (negCode χ) (negCode χ)
  have hB := impFragment_valid hA hneg hneg
  have hBc := impFragment_countable (n := (0 : V)) (φ := negCode χ) (ψ := negCode χ) hAc
  have hT : ⟨(0 : V), T⟩ₖ ∈ impFragment A 0 (negCode χ) (negCode χ) := impFragment_mem _ _ _ _
  obtain ⟨a, ha⟩ := h.explode (ψ := negCode T) k (hB.insert_neg hT)
    (internallyCountable_insert hBc ⟨(0 : V), negCode T⟩ₖ) (by simp)
  obtain ⟨b, hb⟩ := ha.deduction hAC
  obtain ⟨d, hd⟩ := hb.classical_contrapose
  obtain ⟨q, hq⟩ := internalDerivation_identity hA hAc
    (fun t ht ↦ mem_insert.mpr (Or.inr (hΓF t ht))) hneg
  exact hd.mp hq

end ZFVP.Infinitary.Internal
