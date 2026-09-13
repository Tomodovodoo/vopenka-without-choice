import ZFVP.ModelTheory.SchmerlInternalPropositionalDerivation
import ZFVP.ModelTheory.SchmerlInternalSubstitutionBoolean

/-! Quantifier deduction operations with constructed countable fragments. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalDerivation_ordinaryQuantifier {L Γ F n φ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ F)
    (ha : IsOrdinaryQuantifierAxiom L n φ) : ∃ c, IsInternalDerivationCode L Γ n φ c := by
  apply internalDerivation_of_axiom hF hc hΓ
    (d := booleanProofNode n φ 13 ∅) _ (booleanProofNode_label _ _ _ _)
  unfold IsInternalProofNode
  right; right; right; right; right; right; right; right
  exact ⟨n, φ, hφ, rfl, ha⟩

theorem IsInternalDerivationCode.all_imp {L Γ n φ ψ c : V}
    (h : IsInternalDerivationCode L Γ n (allCode (impCode φ ψ)) c) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode (allCode φ) (allCode ψ)) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have ht : ⟨n, allCode (impCode φ ψ)⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hn := (hP.1.node ht).1
  have hφ := hP.1.imp_left_mem (hP.1.all_mem ht)
  have hψ := hP.1.imp_right_mem (hP.1.all_mem ht)
  have hA := allFragment_valid hP.1 hn hφ
  have hAc := allFragment_countable (n := n) (φ := φ) hFc
  have hFA := allFragment_subset F n φ
  have hB := allFragment_valid hA hn (hFA _ hψ)
  have hBc := allFragment_countable (n := n) (φ := ψ) hAc
  have hAB := allFragment_subset (allFragment F n φ) n ψ
  have hK := impFragment_valid hB (hAB _ (allFragment_mem F n φ)) (allFragment_mem _ n ψ)
  have hKc := impFragment_countable (n := n) (φ := allCode φ) (ψ := allCode ψ) hBc
  have hBK := impFragment_subset (allFragment (allFragment F n φ) n ψ) n (allCode φ) (allCode ψ)
  have hT := impFragment_valid hK (hBK _ (hAB _ (hFA _ ht))) (impFragment_mem _ _ _ _)
  obtain ⟨a, ha⟩ := internalDerivation_ordinaryQuantifier hT (impFragment_countable hKc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hBK t (hAB t (hFA t (hP.2.1 t ht)))))
    (impFragment_mem _ _ _ _) ⟨hn, Or.inl ⟨φ, ψ, rfl⟩⟩
  exact ha.mp ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩

theorem IsInternalDerivationCode.imp_trans {L Γ n φ ψ θ c e : V}
    (h : IsInternalDerivationCode L Γ n (impCode φ ψ) c)
    (k : IsInternalDerivationCode L Γ n (impCode ψ θ) e) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode φ θ) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have ht : ⟨n, impCode φ ψ⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  obtain ⟨a, ha⟩ := k.weaken_imp hP.1 hFc (hP.1.imp_left_mem ht)
  exact ha.imp_mp ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩

theorem internalDerivation_vacuous {L Γ F n φ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ F) :
    ∃ c, IsInternalDerivationCode L Γ n (impCode φ (allCode (weakenCode L F n φ))) c := by
  have hn := (hF.node hφ).1
  have hR := renamedFragment_valid hF hn (ω_succ_closed hn) (successorIndices_function hn)
  have hRc := renamedFragment_countable (L := L) (n := n) (m := succ n)
    (r := successorIndices n) hc
  have hw : ⟨succ n, weakenCode L F n φ⟩ₖ ∈ renamedFragment L F n (succ n) (successorIndices n) :=
    renameCode_mem hφ
  let R := renamedFragment L F n (succ n) (successorIndices n)
  have hJ : IsFragment L (F ∪ R) := hF.union hR
  have hJc : IsInternallyCountable (F ∪ R) := internallyCountable_union hc hRc
  have hFJ : F ⊆ F ∪ R := fun _ ht ↦ mem_union_iff.mpr (Or.inl ht)
  have hA := allFragment_valid hJ hn (mem_union_iff.mpr (Or.inr hw))
  have hAc := allFragment_countable (n := n) (φ := weakenCode L F n φ) hJc
  have hJA := allFragment_subset (F ∪ R) n (weakenCode L F n φ)
  have hT := impFragment_valid hA (hJA _ (hFJ _ hφ)) (allFragment_mem _ _ _)
  apply internalDerivation_ordinaryQuantifier hT (impFragment_countable hAc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hJA t (hFJ t (hΓ t ht))))
    (impFragment_mem _ _ _ _)
  exact ⟨hn, Or.inr ⟨F, φ, hF, hφ, rfl⟩⟩

/-- The quantified deduction step. The antecedent is explicitly weakened,
so this operation does not assume any unproved renaming identity. -/
theorem IsInternalDerivationCode.imp_generalize {L Γ F n φ ψ c : V}
    (h : IsInternalDerivationCode L Γ (succ n) (impCode (weakenCode L F n φ) ψ) c)
    (hF : IsFragment L F) (hc : IsInternallyCountable F)
    (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ F) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode φ (allCode ψ)) z := by
  obtain ⟨a, ha⟩ := h.generalize
  obtain ⟨b, hb⟩ := ha.all_imp
  obtain ⟨e, he⟩ := internalDerivation_vacuous hF hc hΓ hφ
  exact he.imp_trans hb

theorem IsInternalDerivationCode.imp_substitute {L Γ H s φ ψ c : V}
    (h : IsInternalDerivationCode L Γ (stateSource s) (impCode φ ψ) c)
    (hH : IsFragment L H) (hs : IsSubstitutionState L ∅ ∅ s)
    (ht : ⟨stateSource s, impCode φ ψ⟩ₖ ∈ H) :
    ∃ z, IsInternalDerivationCode L Γ (stateTarget s)
      (impCode (substituteCode L H s φ) (substituteCode L H s ψ)) z := by
  obtain ⟨z, hz⟩ := h.substitute_from hH hs ht
  rw [substituteCode_imp hH ht] at hz
  exact ⟨z, hz⟩

theorem internalDerivation_hypothesis {L Γ F n φ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ Γ) :
    ∃ c, IsInternalDerivationCode L Γ n φ c := by
  apply internalDerivation_of_axiom hF hc hΓ
    (d := booleanProofNode n φ 0 ∅) _ (booleanProofNode_label _ _ _ _)
  exact Or.inl (Or.inl ⟨n, φ, hΓ _ hφ, Or.inl ⟨rfl, hφ⟩⟩)

theorem IsInternalDerivationCode.mono {L Γ Δ J n φ c : V}
    (h : IsInternalDerivationCode L Γ n φ c) (hJ : IsFragment L J)
    (hJc : IsInternallyCountable J) (hΓΔ : Γ ⊆ Δ) (hΔ : Δ ⊆ J) :
    ∃ z, IsInternalDerivationCode L Δ n φ z := by
  obtain ⟨F, D, d, _, hFc, hDc, hP, hd, hl⟩ := h
  refine ⟨⟨F ∪ J, ⟨D, d⟩ₖ⟩ₖ, F ∪ J, D, d, rfl,
    internallyCountable_union hFc hJc, hDc, ?_, hd, hl⟩
  exact hP.weaken (hP.1.union hJ) hΓΔ
    (fun t ht ↦ mem_union_iff.mpr (Or.inr (hΔ t ht)))
    (fun _ ht ↦ mem_union_iff.mpr (Or.inl ht))

end ZFVP.Infinitary.Internal
