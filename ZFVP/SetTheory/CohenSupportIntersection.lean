import ZFVP.SetTheory.CohenSupportOrbits

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem permutation_value_not_mem_of_fixes {I S π a : V}
    (hπ : IsInternalPermutation I π) (hSI : S ⊆ I)
    (hfix : ∀ i ∈ S, π ‘ i = i) (ha : a ∈ I) (haS : a ∉ S) : π ‘ a ∉ S := by
  intro hin
  have he := injective_value_eq hπ.1 hπ.2.1 ha (hSI _ hin) (hfix _ hin).symm
  exact haS (he.symm ▸ hin)

/-- Finite interpolation by name-fixing permutations, assuming all transpositions away from
`S` fix the name. The induction is internal and applies to nonstandard finite sets. -/
theorem cohenName_finite_interpolation {I S τ π : V}
    (hτ : IsForcingName (cohenConditions I) τ) (hSI : S ⊆ I)
    (htrans : ∀ a ∈ I, ∀ b ∈ I, a ∉ S → b ∉ S →
      nameAction (cohenPermutation I (internalTransposition I a b)) τ = τ)
    (hπ : IsInternalPermutation I π) (hπfix : ∀ i ∈ S, π ‘ i = i)
    {D : V} (hD : IsInternallyFinite D) (hDI : D ⊆ I) :
    ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ S, σ ‘ i = i) ∧
      nameAction (cohenPermutation I σ) τ = τ ∧ ∀ i ∈ D, σ ‘ i = π ‘ i := by
  have key : ∀ D, IsInternallyFinite D → D ⊆ I →
      ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ S, σ ‘ i = i) ∧
        nameAction (cohenPermutation I σ) τ = τ ∧ ∀ i ∈ D, σ ‘ i = π ‘ i := by
    apply internallyFinite_induction (fun D ↦ D ⊆ I →
      ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ S, σ ‘ i = i) ∧
        nameAction (cohenPermutation I σ) τ = τ ∧ ∀ i ∈ D, σ ‘ i = π ‘ i)
      (by definability)
    · intro _
      refine ⟨identity I, internalPermutation_identity I, ?_, ?_, ?_⟩
      · exact fun i hi ↦ identity_value (hSI i hi)
      · rw [cohenPermutation_identity, nameAction_identity hτ]
      · exact fun i hi ↦ (not_mem_empty hi).elim
    · intro A a ih hsub
      have hAI : A ⊆ I := fun i hi ↦ hsub i (mem_insert.mpr (Or.inr hi))
      have haI : a ∈ I := hsub a (mem_insert.mpr (Or.inl rfl))
      obtain ⟨σ, hσ, hσfix, hστ, hagree⟩ := ih hAI
      by_cases he : σ ‘ a = π ‘ a
      · exact ⟨σ, hσ, hσfix, hστ, fun i hi ↦ by
          rcases mem_insert.mp hi with rfl | hi
          · exact he
          · exact hagree i hi⟩
      have haS : a ∉ S := fun ha ↦ he ((hσfix a ha).trans (hπfix a ha).symm)
      have hbI : σ ‘ a ∈ I := function_value_mem hσ.1 haI
      have hcI : π ‘ a ∈ I := function_value_mem hπ.1 haI
      have hbS := permutation_value_not_mem_of_fixes hσ hSI hσfix haI haS
      have hcS := permutation_value_not_mem_of_fixes hπ hSI hπfix haI haS
      let t := internalTransposition I (σ ‘ a) (π ‘ a)
      have ht : IsInternalPermutation I t := internalTransposition_permutation hbI hcI
      refine ⟨compose σ t, hσ.comp ht, ?_, ?_, ?_⟩
      · intro i hi
        rw [value_compose_of_mem_function hσ.1 ht.1 (hSI i hi), hσfix i hi]
        exact internalTransposition_fixed (hSI i hi)
          (fun hei ↦ hbS (hei ▸ hi)) (fun hei ↦ hcS (hei ▸ hi))
      · rw [cohenPermutation_compose hσ ht,
          ← nameAction_compose (cohenPermutation_automorphism hσ).1
            (cohenPermutation_automorphism ht).1 hτ, hστ]
        exact htrans _ hbI _ hcI hbS hcS
      · intro i hi
        rw [value_compose_of_mem_function hσ.1 ht.1 (hsub i hi)]
        rcases mem_insert.mp hi with rfl | hi
        · exact internalTransposition_left hbI
        · have hia : i ≠ a := fun h ↦ he (h ▸ hagree i hi)
          have hib : σ ‘ i ≠ σ ‘ a := fun h ↦
            hia (injective_value_eq hσ.1 hσ.2.1 (hAI i hi) haI h)
          have hic : σ ‘ i ≠ π ‘ a := fun h ↦
            hia (injective_value_eq hπ.1 hπ.2.1 (hAI i hi) haI ((hagree i hi).symm.trans h))
          exact (internalTransposition_fixed (function_value_mem hσ.1 (hAI i hi)) hib hic).trans
            (hagree i hi)
  exact key D hD hDI

/-- For a finitely supported name, testing all transpositions away from `S` suffices to show
that every permutation fixing `S` fixes the name. -/
theorem cohenName_support_of_transpositions {I S τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions I) (cohenGroup I) (cohenFilter I) τ)
    (hSI : S ⊆ I)
    (htrans : ∀ a ∈ I, ∀ b ∈ I, a ∉ S → b ∉ S →
      nameAction (cohenPermutation I (internalTransposition I a b)) τ = τ) :
    ∀ π, IsInternalPermutation I π → (∀ i ∈ S, π ‘ i = i) →
      nameAction (cohenPermutation I π) τ = τ := by
  intro π hπ hπfix
  obtain ⟨D, hDI, hDf, hsupport⟩ := cohenName_finiteSupport hτ
  obtain ⟨σ, hσ, _, hστ, hagree⟩ :=
    cohenName_finite_interpolation hτ.1 hSI htrans hπ hπfix hDf hDI
  exact (cohenNameAction_eq_of_agree_on_support hτ.1 hDI hsupport hσ hπ hagree).symm.trans hστ

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem transpositionValue_triple {a b c x : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    transpositionValue a c (transpositionValue b c (transpositionValue a c x)) =
      transpositionValue a b x := by
  classical
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [transpositionValue]

private theorem cohenName_transposition_fixed_of_two_supports {E F τ a b : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E) (hFf : IsInternallyFinite F)
    (hE : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ)
    (hF : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ F, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ)
    (hFω : F ⊆ (ω : V)) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
    (haE : a ∉ E) (hbF : b ∉ F) :
    nameAction (cohenPermutation (ω : V) (internalTransposition (ω : V) a b)) τ = τ := by
  classical
  by_cases hab : a = b
  · subst b
    apply hE _ (internalTransposition_permutation ha ha)
    intro i hi
    exact internalTransposition_fixed (hEω i hi) (fun h ↦ haE (h ▸ hi))
      (fun h ↦ haE (h ▸ hi))
  obtain ⟨c, hc, hcout⟩ := internallyFinite_fresh_natural
    (internallyFinite_insert (internallyFinite_insert (internallyFinite_union hEf hFf) a) b)
  have hcb : c ≠ b := fun h ↦ hcout (mem_insert.mpr (Or.inl h))
  have hca : c ≠ a := fun h ↦ hcout (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl h))))
  have hcE : c ∉ E := fun h ↦ hcout
    (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl h))))))
  have hcF : c ∉ F := fun h ↦ hcout
    (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr h))))))
  let p := internalTransposition (ω : V) a c
  let q := internalTransposition (ω : V) b c
  have hp : IsInternalPermutation (ω : V) p := internalTransposition_permutation ha hc
  have hq : IsInternalPermutation (ω : V) q := internalTransposition_permutation hb hc
  have hpfix : nameAction (cohenPermutation (ω : V) p) τ = τ := by
    apply hE p hp
    exact fun i hi ↦ internalTransposition_fixed (hEω i hi)
      (fun h ↦ haE (h ▸ hi)) (fun h ↦ hcE (h ▸ hi))
  have hqfix : nameAction (cohenPermutation (ω : V) q) τ = τ := by
    apply hF q hq
    exact fun i hi ↦ internalTransposition_fixed (hFω i hi)
      (fun h ↦ hbF (h ▸ hi)) (fun h ↦ hcF (h ▸ hi))
  have htriple : nameAction (cohenPermutation (ω : V) (compose (compose p q) p)) τ = τ := by
    rw [cohenPermutation_compose (hp.comp hq) hp,
      ← nameAction_compose (cohenPermutation_automorphism (hp.comp hq)).1
        (cohenPermutation_automorphism hp).1 hτ,
      cohenPermutation_compose hp hq,
      ← nameAction_compose (cohenPermutation_automorphism hp).1
        (cohenPermutation_automorphism hq).1 hτ,
      hpfix, hqfix, hpfix]
  have he := cohenNameAction_eq_of_agree_on_support hτ hEω hE
    ((hp.comp hq).comp hp) (internalTransposition_permutation ha hb) (by
      intro i hi
      rw [value_compose_of_mem_function (hp.comp hq).1 hp.1 (hEω i hi),
        value_compose_of_mem_function hp.1 hq.1 (hEω i hi)]
      rw [show p = internalTransposition (ω : V) a c from rfl,
        internalTransposition_value (function_value_mem hq.1 (function_value_mem hp.1 (hEω i hi))),
        show q = internalTransposition (ω : V) b c from rfl,
        internalTransposition_value (function_value_mem hp.1 (hEω i hi)),
        internalTransposition_value (hEω i hi), internalTransposition_value (hEω i hi)]
      exact transpositionValue_triple hab hca.symm hcb.symm)
  exact he.symm.trans htriple

/-- Finite supports of hereditarily symmetric Cohen names are closed under intersection.
This statement concerns ground names; it does not posit an action on the fixed-generic quotient. -/
theorem cohenName_support_intersection {E F τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (hFω : F ⊆ (ω : V)) (hFf : IsInternallyFinite F)
    (hE : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ)
    (hF : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ F, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ) :
    ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E ∩ F, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ := by
  apply cohenName_support_of_transpositions hτ (fun i hi ↦ hEω i (mem_inter_iff.mp hi).1)
  intro a ha b hb haEF hbEF
  by_cases haE : a ∈ E
  · have haF : a ∉ F := fun h ↦ haEF (mem_inter_iff.mpr ⟨haE, h⟩)
    by_cases hbF : b ∈ F
    · have hbE : b ∉ E := fun h ↦ hbEF (mem_inter_iff.mpr ⟨h, hbF⟩)
      exact cohenName_transposition_fixed_of_two_supports hτ.1 hFω hFf hEf hF hE hEω
        ha hb haF hbE
    · apply hF _ (internalTransposition_permutation ha hb)
      exact fun i hi ↦ internalTransposition_fixed (hFω i hi)
        (fun h ↦ haF (h ▸ hi)) (fun h ↦ hbF (h ▸ hi))
  · by_cases hbE : b ∈ E
    · have hbF : b ∉ F := fun h ↦ hbEF (mem_inter_iff.mpr ⟨hbE, h⟩)
      exact cohenName_transposition_fixed_of_two_supports hτ.1 hEω hEf hFf hE hF hFω
        ha hb haE hbF
    · apply hE _ (internalTransposition_permutation ha hb)
      exact fun i hi ↦ internalTransposition_fixed (hEω i hi)
        (fun h ↦ haE (h ▸ hi)) (fun h ↦ hbE (h ▸ hi))

end ZFVP
