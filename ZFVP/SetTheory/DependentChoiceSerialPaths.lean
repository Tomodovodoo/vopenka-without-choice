import ZFVP.SetTheory.DependentChoicePaths

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoicePath_of_serial_paths {γ A R : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ) (hA : IsNonempty A)
    (hserial : ∀ s ∈ shorterSequences γ A,
      IsDependentChoicePath A R (domain s) s → ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) :
    ∃ f, IsDependentChoicePath A R γ f := by
  classical
  let Q : V := {z ∈ shorterSequences γ A ×ˢ A ;
    IsDependentChoicePath A R (domain (kpair.π₁ z)) (kpair.π₁ z) → z ∈ R}
  have hQ (s x : V) : ⟨s, x⟩ₖ ∈ Q ↔ s ∈ shorterSequences γ A ∧ x ∈ A ∧
      (IsDependentChoicePath A R (domain s) s → ⟨s, x⟩ₖ ∈ R) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair]
    tauto
  have hserialQ : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ Q := by
    intro s hs
    by_cases hpath : IsDependentChoicePath A R (domain s) s
    · obtain ⟨x, hx, hsx⟩ := hserial s hs hpath
      exact ⟨x, hx, (hQ s x).mpr ⟨hs, hx, fun _ ↦ hsx⟩⟩
    · obtain ⟨x, hx⟩ := hA
      exact ⟨x, hx, (hQ s x).mpr ⟨hs, hx, fun h ↦ False.elim (hpath h)⟩⟩
  obtain ⟨f, hf, hstep⟩ := hDC A Q hA hserialQ
  let := IsFunction.of_mem hf
  have hprogress : ∀ i : Ordinal V, i.val ∈ γ → ⟨f ↾ i.val, f ‘ i.val⟩ₖ ∈ R := by
    apply transfinite_induction (fun i ↦ i ∈ γ → ⟨f ↾ i, f ‘ i⟩ₖ ∈ R) (by definability)
    intro i ih hi
    have hisub : i.val ⊆ γ := IsOrdinal.toIsTransitive.transitive _ hi
    have hfi := function_restrict_mem hf hisub
    have hgood : IsDependentChoicePath A R i.val (f ↾ i.val) := by
      refine ⟨hfi, ?_⟩
      intro j hj
      let := IsOrdinal.of_mem hj
      rw [restrict_restrict_of_subset (IsOrdinal.toIsTransitive.transitive _ hj),
        value_restrict (by rw [domain_eq_of_mem_function hf]; exact hisub j hj) hj]
      exact ih (IsOrdinal.toOrdinal j) hj (hisub j hj)
    have hh := ((hQ _ _).mp (hstep i.val hi)).2.2
    rw [domain_eq_of_mem_function hfi] at hh
    exact hh hgood
  refine ⟨f, hf, fun i hi ↦ ?_⟩
  let := IsOrdinal.of_mem hi
  exact hprogress (IsOrdinal.toOrdinal i) hi

end ZFVP
