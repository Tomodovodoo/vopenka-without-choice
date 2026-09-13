import ZFVP.ModelTheory.SchmerlInternalProofExtension

/-! Finite constructor closure of actual internal fragments, with countability
preserved in ZF. No choice of external enumerations is used. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsFragment.insert_node {L F n φ : V} (hF : IsFragment L F) (hφ : IsNode L F n φ) :
    IsFragment L (insert ⟨n, φ⟩ₖ F) := by
  have hsub : F ⊆ insert ⟨n, φ⟩ₖ F := fun _ hx ↦ mem_insert.mpr (Or.inr hx)
  refine ⟨hF.1, ?_⟩
  intro t ht
  rcases mem_insert.mp ht with rfl | ht
  · simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨trivial, hφ.mono hsub⟩
  · exact ⟨(hF.2 t ht).1, (hF.2 t ht).2.mono hsub⟩

theorem IsFragment.insert_neg {L F n φ : V} (hF : IsFragment L F) (hφ : ⟨n, φ⟩ₖ ∈ F) :
    IsFragment L (insert ⟨n, negCode φ⟩ₖ F) :=
  hF.insert_node ⟨(hF.node hφ).1, Or.inr (Or.inl ⟨φ, rfl, hφ⟩)⟩

theorem IsFragment.insert_exs {L F n φ : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hφ : ⟨succ n, φ⟩ₖ ∈ F) :
    IsFragment L (insert ⟨n, exsCode φ⟩ₖ F) :=
  hF.insert_node ⟨hn, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, rfl, hφ⟩)))⟩

theorem IsFragment.insert_conj {L F n f : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hf : IsFunction f) (hd : domain f = (ω : V))
    (hφ : ∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F) : IsFragment L (insert ⟨n, conjCode f⟩ₖ F) :=
  hF.insert_node ⟨hn, Or.inr (Or.inr (Or.inl ⟨f, hf, hd, rfl, hφ⟩))⟩

noncomputable def allFragment (F n φ : V) : V :=
  insert ⟨n, allCode φ⟩ₖ (insert ⟨n, exsCode (negCode φ)⟩ₖ (insert ⟨succ n, negCode φ⟩ₖ F))

instance allFragment_definable : ℒₛₑₜ-function₃[V] allFragment := by
  unfold allFragment
  definability

theorem allFragment_subset (F n φ : V) : F ⊆ allFragment F n φ := by
  intro t ht
  simp [allFragment, ht]

theorem allFragment_mem (F n φ : V) : ⟨n, allCode φ⟩ₖ ∈ allFragment F n φ := by
  simp [allFragment]

theorem allFragment_valid {L F n φ : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hφ : ⟨succ n, φ⟩ₖ ∈ F) : IsFragment L (allFragment F n φ) := by
  have hneg := hF.insert_neg hφ
  have hex := hneg.insert_exs (φ := negCode φ) hn (by simp)
  exact hex.insert_neg (φ := exsCode (negCode φ)) (by simp)

theorem allFragment_countable {F n φ : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (allFragment F n φ) :=
  internallyCountable_insert (internallyCountable_insert (internallyCountable_insert hF _) _) _

theorem IsFragment.insert_and {L F n φ ψ : V} (hF : IsFragment L F)
    (hφ : ⟨n, φ⟩ₖ ∈ F) (hψ : ⟨n, ψ⟩ₖ ∈ F) :
    IsFragment L (insert ⟨n, andCode φ ψ⟩ₖ F) := by
  apply hF.insert_conj (hF.node hφ).1 inferInstance (domain_binaryCodeSequence φ ψ)
  intro i hi
  rw [value_binaryCodeSequence _ _ hi]
  unfold binaryCodeValue
  split <;> assumption

noncomputable def impFragment (F n φ ψ : V) : V :=
  insert ⟨n, impCode φ ψ⟩ₖ
    (insert ⟨n, andCode (negCode (negCode φ)) (negCode ψ)⟩ₖ
      (insert ⟨n, negCode ψ⟩ₖ (insert ⟨n, negCode (negCode φ)⟩ₖ
        (insert ⟨n, negCode φ⟩ₖ F))))

instance impFragment_definable : ℒₛₑₜ-function₄[V] impFragment := by
  unfold impFragment
  definability

theorem impFragment_subset (F n φ ψ : V) : F ⊆ impFragment F n φ ψ := by
  intro t ht
  simp [impFragment, ht]

theorem impFragment_mem (F n φ ψ : V) : ⟨n, impCode φ ψ⟩ₖ ∈ impFragment F n φ ψ := by
  simp [impFragment]

theorem impFragment_valid {L F n φ ψ : V} (hF : IsFragment L F)
    (hφ : ⟨n, φ⟩ₖ ∈ F) (hψ : ⟨n, ψ⟩ₖ ∈ F) : IsFragment L (impFragment F n φ ψ) := by
  have h₁ := hF.insert_neg hφ
  have h₂ := h₁.insert_neg (n := n) (φ := negCode φ) (by simp)
  have h₃ := h₂.insert_neg (n := n) (φ := ψ) (by simp [hψ])
  have h₄ := h₃.insert_and (n := n) (φ := negCode (negCode φ)) (ψ := negCode ψ) (by simp) (by simp)
  exact h₄.insert_neg (n := n) (φ := andCode (negCode (negCode φ)) (negCode ψ)) (by simp)

theorem impFragment_countable {F n φ ψ : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (impFragment F n φ ψ) :=
  internallyCountable_insert (internallyCountable_insert (internallyCountable_insert
    (internallyCountable_insert (internallyCountable_insert hF _) _) _) _) _

end ZFVP.Infinitary.Internal
