import ZFVP.ModelTheory.StandardProofLists

/-! Building internally checked proofs from finitely many externally supplied inference steps. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def StandardCodedProvable (T n Γ : V) : Prop :=
  ∃ xs : List V, IsOpenCodedProofList T (xs ++ [⟨n, Γ⟩ₖ])

theorem StandardCodedProvable.to_internal {T n Γ : V} (h : StandardCodedProvable T n Γ) :
    ∃ p, IsOpenCodedSequentProof T p n Γ := by
  obtain ⟨xs, hx⟩ := h
  exact ⟨_, hx.to_internal⟩

theorem StandardCodedProvable.valid {T n Γ : V} (h : StandardCodedProvable T n Γ) :
    IsCodedSequent n Γ := by
  obtain ⟨xs, hx⟩ := h
  obtain ⟨m, Δ, he, hv, _⟩ := hx ⟨xs.length, by simp⟩
  have hpair : ⟨n, Γ⟩ₖ = ⟨m, Δ⟩ₖ := by simpa using he
  obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair
  exact hv

theorem StandardCodedProvable.of_rule {T n Γ : V} (hv : IsCodedSequent n Γ)
    (hr : IsOpenCodedSequentRule T ∅ n Γ) : StandardCodedProvable T n Γ :=
  ⟨[], (isOpenCodedProofList_nil T).snoc hv hr⟩

theorem StandardCodedProvable.unary {T m Δ n Γ : V} (hp : StandardCodedProvable T m Δ)
    (hv : IsCodedSequent n Γ) (hr : IsOpenCodedSequentRule T {⟨m, Δ⟩ₖ} n Γ) :
    StandardCodedProvable T n Γ := by
  obtain ⟨xs, hx⟩ := hp
  refine ⟨xs ++ [⟨m, Δ⟩ₖ], hx.snoc hv (hr.mono ?_)⟩
  intro x hx
  have he : x = ⟨m, Δ⟩ₖ := by simpa using hx
  simp [he]

theorem StandardCodedProvable.binary {T m Δ k Ξ n Γ : V}
    (hp : StandardCodedProvable T m Δ) (hq : StandardCodedProvable T k Ξ)
    (hv : IsCodedSequent n Γ) (hr : IsOpenCodedSequentRule T {⟨m, Δ⟩ₖ, ⟨k, Ξ⟩ₖ} n Γ) :
    StandardCodedProvable T n Γ := by
  obtain ⟨xs, hx⟩ := hp
  obtain ⟨ys, hy⟩ := hq
  refine ⟨(xs ++ [⟨m, Δ⟩ₖ]) ++ (ys ++ [⟨k, Ξ⟩ₖ]), (hx.append hy).snoc hv (hr.mono ?_)⟩
  intro x hx
  simp only [mem_insert, mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp

theorem isCodedSequent_standardListSet {n : V} (hn : n ∈ (ω : V)) (xs : List V)
    (hx : ∀ φ ∈ xs, φ ∈ formulaSet membershipLanguageCode ∅ n) :
    IsCodedSequent n (standardListSet xs) :=
  ⟨hn, standardListSet_internallyFinite xs, fun φ hφ ↦ hx φ ((mem_standardListSet xs φ).mp hφ)⟩

theorem StandardCodedProvable.axiom {T n φ : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode n φ) (hT : ⟨n, φ⟩ₖ ∈ T) :
    StandardCodedProvable T n {φ} := by
  apply StandardCodedProvable.of_rule
  · simpa [standardListSet] using isCodedSequent_standardListSet hn [φ] (by simpa using hφ.valid)
  · exact Or.inr ⟨φ, hT, rfl⟩

theorem StandardCodedProvable.identity (T : V) {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T n {φ, negateFormula membershipLanguageCode ∅ n φ} := by
  apply StandardCodedProvable.of_rule
  · have hneg := negateFormula_mem membershipLanguageCode_valid hφ
    simpa [standardListSet] using isCodedSequent_standardListSet hn
      [φ, negateFormula membershipLanguageCode ∅ n φ] (by simpa using And.intro hφ hneg)
  · exact Or.inl (Or.inr (Or.inl ⟨φ, hφ, rfl⟩))

theorem StandardCodedProvable.verum (T : V) {n : V} (hn : n ∈ (ω : V)) :
    StandardCodedProvable T n {truthCode} := by
  apply StandardCodedProvable.of_rule
  · simpa [standardListSet] using isCodedSequent_standardListSet hn [truthCode]
      (by
        have ht : truthCode ∈ formulaSet (membershipLanguageCode : V) ∅ n :=
          (mem_formulaSet_iff _ _ _ _).mpr (formulaFamily_closed membershipLanguageCode_valid ∅ n hn).1.1
        simpa using ht)
  · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))

theorem OpenCodedSequentConsistent.not_standard_refutation {T : V}
    (hT : OpenCodedSequentConsistent T) : ¬StandardCodedProvable T 0 ∅ :=
  fun h ↦ hT h.to_internal

end ZFVP
