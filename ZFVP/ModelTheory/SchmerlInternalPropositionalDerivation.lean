import ZFVP.ModelTheory.SchmerlInternalProofComposition

/-! Constructed propositional derivations used to discharge assumptions in the
internal calculus. All new formula labels lie in explicitly countable fragments. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalDerivation_boolean {L Γ F n φ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ F)
    (ha : IsBooleanAxiom φ) : ∃ c, IsInternalDerivationCode L Γ n φ c := by
  apply internalDerivation_of_axiom hF hc hΓ
    (d := booleanProofNode n φ 1 ∅) _ (booleanProofNode_label _ _ _ _)
  exact Or.inl (Or.inl ⟨n, φ, hφ, Or.inr (Or.inl ⟨rfl, ha⟩)⟩)

theorem internalDerivation_k {L Γ F n φ ψ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F)
    (hφ : ⟨n, φ⟩ₖ ∈ F) (hψ : ⟨n, ψ⟩ₖ ∈ F) :
    ∃ c, IsInternalDerivationCode L Γ n (impCode φ (impCode ψ φ)) c := by
  have hK := impFragment_valid hF hψ hφ
  have hKc := impFragment_countable (n := n) (φ := ψ) (ψ := φ) hc
  have hFK := impFragment_subset F n ψ φ
  have hT := impFragment_valid hK (hFK _ hφ) (impFragment_mem F n ψ φ)
  apply internalDerivation_boolean hT (impFragment_countable hKc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hFK t (hΓ t ht)))
    (impFragment_mem _ _ _ _)
  exact Or.inl ⟨φ, ψ, rfl⟩

theorem IsInternalDerivationCode.weaken_imp {L Γ H n φ ψ c : V}
    (h : IsInternalDerivationCode L Γ n φ c) (hH : IsFragment L H)
    (hHc : IsInternallyCountable H) (hψ : ⟨n, ψ⟩ₖ ∈ H) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode ψ φ) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have hφ : ⟨n, φ⟩ₖ ∈ F := by simpa only [hl] using (hP.2.2 d hd).label_mem
  obtain ⟨e, he'⟩ := internalDerivation_k (hP.1.union hH) (internallyCountable_union hFc hHc)
    (fun t ht ↦ mem_union_iff.mpr (Or.inl (hP.2.1 t ht)))
    (mem_union_iff.mpr (Or.inl hφ)) (mem_union_iff.mpr (Or.inr hψ))
  exact he'.mp ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩

theorem IsInternalDerivationCode.imp_mp {L Γ n φ ψ θ c e : V}
    (h : IsInternalDerivationCode L Γ n (impCode φ (impCode ψ θ)) c)
    (k : IsInternalDerivationCode L Γ n (impCode φ ψ) e) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode φ θ) z := by
  obtain ⟨F, D, d, hc, hFc, hDc, hP, hd, hl⟩ := h
  obtain ⟨H, E, q, he, hHc, hEc, hQ, hq, hqL⟩ := k
  have hp : ⟨n, impCode φ (impCode ψ θ)⟩ₖ ∈ F ∪ H := by
    apply mem_union_iff.mpr; apply Or.inl
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hq' : ⟨n, impCode φ ψ⟩ₖ ∈ F ∪ H := by
    apply mem_union_iff.mpr; apply Or.inr
    simpa only [hqL] using (hQ.2.2 q hq).label_mem
  have hJ := hP.1.union hQ.1
  have hJc := internallyCountable_union hFc hHc
  have hΓ : Γ ⊆ F ∪ H := fun t ht ↦ mem_union_iff.mpr (Or.inl (hP.2.1 t ht))
  have hA := impFragment_valid hJ (hJ.imp_left_mem hp) (hJ.imp_right_mem (hJ.imp_right_mem hp))
  have hAc := impFragment_countable (n := n) (φ := φ) (ψ := θ) hJc
  have hJA := impFragment_subset (F ∪ H) n φ θ
  have hB := impFragment_valid hA (hJA _ hq') (impFragment_mem (F ∪ H) n φ θ)
  have hBc := impFragment_countable (n := n) (φ := impCode φ ψ) (ψ := impCode φ θ) hAc
  have hAB := impFragment_subset (impFragment (F ∪ H) n φ θ) n (impCode φ ψ) (impCode φ θ)
  have hT := impFragment_valid hB (hAB _ (hJA _ hp)) (impFragment_mem _ _ _ _)
  obtain ⟨a, ha⟩ := internalDerivation_boolean hT (impFragment_countable hBc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hAB t (hJA t (hΓ t ht))))
    (impFragment_mem _ _ _ _) (Or.inr (Or.inl ⟨φ, ψ, θ, rfl⟩))
  obtain ⟨b, hb⟩ := ha.mp ⟨F, D, d, hc, hFc, hDc, hP, hd, hl⟩
  exact hb.mp ⟨H, E, q, he, hHc, hEc, hQ, hq, hqL⟩

theorem internalDerivation_identity {L Γ F n φ : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F) (hφ : ⟨n, φ⟩ₖ ∈ F) :
    ∃ c, IsInternalDerivationCode L Γ n (impCode φ φ) c := by
  obtain ⟨b, hb⟩ := internalDerivation_k hF hc hΓ hφ hφ
  have hA := impFragment_valid hF hφ hφ
  have hFA := impFragment_subset F n φ φ
  obtain ⟨c, hc⟩ := internalDerivation_k hA (impFragment_countable hc)
    (fun t ht ↦ hFA t (hΓ t ht)) (hFA _ hφ) (impFragment_mem F n φ φ)
  exact hc.imp_mp hb

theorem internalDerivation_imp_conjunction {L Γ n φ f : V} (hAC : InternalChoice V)
    (hf : IsFunction f) (hfd : domain f = (ω : V))
    (h : ∀ i ∈ (ω : V), ∃ c, IsInternalDerivationCode L Γ n (impCode φ (f ‘ i)) c) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode φ (conjCode f)) z := by
  let g := definableGraph (ω : V) (fun i ↦ impCode φ (f ‘ i)) (by definability)
  have hg : IsFunction g := inferInstanceAs (IsFunction (definableGraph _ _ _))
  have hgd : domain g = (ω : V) := domain_definableGraph _ _ _
  have hgv (i : V) (hi : i ∈ (ω : V)) : g ‘ i = impCode φ (f ‘ i) :=
    value_definableGraph _ _ _ hi
  obtain ⟨c, hc⟩ := internalDerivation_conjunction hAC hg hgd (fun i hi ↦ by
    rw [hgv i hi]; exact h i hi)
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := hc
  have hconj : ⟨n, conjCode g⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hi (i : V) (hi : i ∈ (ω : V)) : ⟨n, impCode φ (f ‘ i)⟩ₖ ∈ F := by
    simpa only [hgv i hi] using (hP.1.conj_data hconj).2.2 i hi
  have hφ := hP.1.imp_left_mem (hi 0 (by simp))
  have hA := hP.1.insert_conj (hP.1.node hconj).1 hf hfd
    (fun i hω ↦ hP.1.imp_right_mem (hi i hω))
  have hAc := internallyCountable_insert hFc ⟨n, conjCode f⟩ₖ
  have hFA : F ⊆ insert ⟨n, conjCode f⟩ₖ F := fun _ ht ↦ mem_insert.mpr (Or.inr ht)
  have hB := impFragment_valid (ψ := conjCode f) hA (hFA _ hφ) (by simp)
  have hBc := impFragment_countable (n := n) (φ := φ) (ψ := conjCode f) hAc
  have hAB := impFragment_subset (insert ⟨n, conjCode f⟩ₖ F) n φ (conjCode f)
  have hT := impFragment_valid hB (hAB _ (hFA _ hconj)) (impFragment_mem _ _ _ _)
  obtain ⟨a, ha⟩ := internalDerivation_boolean hT (impFragment_countable hBc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hAB t (hFA t (hP.2.1 t ht))))
    (impFragment_mem _ _ _ _)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, f, g, hf, hfd, hg, hgd, hgv, rfl⟩)))))
  exact ha.mp ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩

theorem IsInternalDerivationCode.conj_elim {L Γ n f c i : V}
    (h : IsInternalDerivationCode L Γ n (conjCode f) c) (hi : i ∈ (ω : V)) :
    ∃ z, IsInternalDerivationCode L Γ n (f ‘ i) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have ht : ⟨n, conjCode f⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hf := hP.1.conj_data ht
  have hT := impFragment_valid hP.1 ht (hf.2.2 i hi)
  obtain ⟨a, ha⟩ := internalDerivation_boolean hT (impFragment_countable hFc)
    (fun t ht ↦ impFragment_subset _ _ _ _ t (hP.2.1 t ht)) (impFragment_mem _ _ _ _)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, i, hf.1, hf.2.1, hi, rfl⟩)))))
  exact ha.mp ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩

end ZFVP.Infinitary.Internal
