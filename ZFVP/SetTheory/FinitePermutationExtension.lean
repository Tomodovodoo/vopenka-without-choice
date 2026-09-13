import ZFVP.SetTheory.InternalTranspositions
import ZFVP.SetTheory.FiniteNaturalSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem protected_value_not_mem {I E σ a : V}
    (hσ : IsInternalPermutation I σ) (hEI : E ⊆ I)
    (hfix : ∀ i ∈ E, σ ‘ i = i) (ha : a ∈ I) (haE : a ∉ E) : σ ‘ a ∉ E := by
  intro hin
  have he := injective_value_eq hσ.1 hσ.2.1 ha (hEI _ hin) (hfix _ hin).symm
  exact haE (he.symm ▸ hin)

/-- An internal injection on a finite domain extends to an internal permutation fixing a
protected set, provided the prescribed values respect that set. The induction is internal. -/
theorem finite_injection_extend_fixing {I E D f : V}
    (hEI : E ⊆ I) (hDI : D ⊆ I) (hD : IsInternallyFinite D)
    (hf : f ∈ I ^ D) (hfi : Injective f)
    (hfix : ∀ i ∈ D, i ∈ E → f ‘ i = i)
    (havoid : ∀ i ∈ D, i ∉ E → f ‘ i ∉ E) :
    ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
      ∀ i ∈ D, σ ‘ i = f ‘ i := by
  have key : ∀ A, IsInternallyFinite A → A ⊆ D →
      ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
        ∀ i ∈ A, σ ‘ i = f ‘ i := by
    apply internallyFinite_induction (fun A ↦ A ⊆ D →
      ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
        ∀ i ∈ A, σ ‘ i = f ‘ i) (by definability)
    · intro _
      exact ⟨identity I, internalPermutation_identity I,
        fun i hi ↦ identity_value (hEI i hi), fun i hi ↦ (not_mem_empty hi).elim⟩
    · intro A a ih hsub
      have hAD : A ⊆ D := fun i hi ↦ hsub i (mem_insert.mpr (Or.inr hi))
      have haD : a ∈ D := hsub a (mem_insert.mpr (Or.inl rfl))
      have haI : a ∈ I := hDI a haD
      obtain ⟨σ, hσ, hσfix, hagree⟩ := ih hAD
      by_cases he : σ ‘ a = f ‘ a
      · exact ⟨σ, hσ, hσfix, fun i hi ↦ by
          rcases mem_insert.mp hi with rfl | hi
          · exact he
          · exact hagree i hi⟩
      have haE : a ∉ E := fun ha ↦ he ((hσfix a ha).trans (hfix a haD ha).symm)
      have hbI : σ ‘ a ∈ I := function_value_mem hσ.1 haI
      have hcI : f ‘ a ∈ I := function_value_mem hf haD
      have hbE := protected_value_not_mem hσ hEI hσfix haI haE
      have hcE := havoid a haD haE
      let t := internalTransposition I (σ ‘ a) (f ‘ a)
      have ht : IsInternalPermutation I t := internalTransposition_permutation hbI hcI
      refine ⟨compose σ t, hσ.comp ht, ?_, ?_⟩
      · intro i hi
        rw [value_compose_of_mem_function hσ.1 ht.1 (hEI i hi), hσfix i hi]
        exact internalTransposition_fixed (hEI i hi)
          (fun hei ↦ hbE (hei ▸ hi)) (fun hei ↦ hcE (hei ▸ hi))
      · intro i hi
        rw [value_compose_of_mem_function hσ.1 ht.1 (hDI i (hsub i hi))]
        rcases mem_insert.mp hi with rfl | hi
        · exact internalTransposition_left hbI
        · have hia : i ≠ a := fun h ↦ he (h ▸ hagree i hi)
          have hib : σ ‘ i ≠ σ ‘ a := fun h ↦
            hia (injective_value_eq hσ.1 hσ.2.1 (hDI i (hAD i hi)) haI h)
          have hic : σ ‘ i ≠ f ‘ a := fun h ↦
            hia (injective_value_eq hf hfi (hAD i hi) haD ((hagree i hi).symm.trans h))
          exact (internalTransposition_fixed (function_value_mem hσ.1 (hDI i (hAD i hi)))
            hib hic).trans (hagree i hi)
  exact key D hD (fun _ hi ↦ hi)

/-- Move a finite set away from another finite set while fixing a disjoint protected set. -/
theorem exists_permutation_moving_fixing {E X Y : V}
    (hE : IsInternallyFinite E) (hEω : E ⊆ (ω : V))
    (hX : IsInternallyFinite X) (hXω : X ⊆ (ω : V))
    (hY : IsInternallyFinite Y) (_hYω : Y ⊆ (ω : V))
    (hXE : ∀ i ∈ X, i ∉ E) :
    ∃ σ, IsInternalPermutation (ω : V) σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
      ∀ i ∈ X, σ ‘ i ∉ Y := by
  have key : ∀ X, IsInternallyFinite X → IsInternallyFinite X ∧
      (X ⊆ (ω : V) → (∀ i ∈ X, i ∉ E) →
        ∃ σ, IsInternalPermutation (ω : V) σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
          ∀ i ∈ X, σ ‘ i ∉ Y) := by
    apply internallyFinite_induction (fun X ↦ IsInternallyFinite X ∧
      (X ⊆ (ω : V) → (∀ i ∈ X, i ∉ E) →
        ∃ σ, IsInternalPermutation (ω : V) σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
          ∀ i ∈ X, σ ‘ i ∉ Y)) (by definability)
    · exact ⟨internallyFinite_empty, fun _ _ ↦
        ⟨identity ω, internalPermutation_identity ω, fun i hi ↦ identity_value (hEω i hi),
          fun n hn ↦ (not_mem_empty hn).elim⟩⟩
    · intro A a ⟨hAfin, ih⟩
      refine ⟨internallyFinite_insert hAfin a, fun hsub hdisj ↦ ?_⟩
      have hAω : A ⊆ (ω : V) := fun z hz ↦ hsub z (mem_insert.mpr (Or.inr hz))
      have haω : a ∈ (ω : V) := hsub a (mem_insert.mpr (Or.inl rfl))
      obtain ⟨σ, hσ, hfix, hmove⟩ := ih hAω
        (fun i hi ↦ hdisj i (mem_insert.mpr (Or.inr hi)))
      by_cases haA : a ∈ A
      · exact ⟨σ, hσ, hfix, fun n hn ↦ by
          rcases mem_insert.mp hn with rfl | hn
          · exact hmove _ haA
          · exact hmove n hn⟩
      have himg : IsInternallyFinite (repl (fun n ↦ σ ‘ n) (by definability) (insert a A)) :=
        internallyFinite_repl _ _ (internallyFinite_insert hAfin a)
      obtain ⟨m, hm, hmn⟩ := internallyFinite_fresh_natural
        (internallyFinite_union (internallyFinite_union hY hE) himg)
      have hmY : m ∉ Y := fun h ↦ hmn
        (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl h))))
      have hmE : m ∉ E := fun h ↦ hmn
        (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr h))))
      have hmimg : ∀ n ∈ insert a A, σ ‘ n ≠ m := fun n hn h ↦
        hmn (mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨n, hn, h.symm⟩)))
      have hσa : σ ‘ a ∈ (ω : V) := function_value_mem hσ.1 haω
      have hσaE : σ ‘ a ∉ E := protected_value_not_mem hσ hEω hfix haω
        (hdisj a (mem_insert.mpr (Or.inl rfl)))
      let t := internalTransposition (ω : V) (σ ‘ a) m
      have ht : IsInternalPermutation (ω : V) t := internalTransposition_permutation hσa hm
      refine ⟨compose σ t, hσ.comp ht, ?_, ?_⟩
      · intro i hi
        rw [value_compose_of_mem_function hσ.1 ht.1 (hEω i hi), hfix i hi]
        exact internalTransposition_fixed (hEω i hi)
          (fun he ↦ hσaE (he ▸ hi)) (fun he ↦ hmE (he ▸ hi))
      · intro n hn
        rw [value_compose_of_mem_function hσ.1 ht.1 (hsub n hn)]
        rcases mem_insert.mp hn with rfl | hnA
        · rw [internalTransposition_left hσa]
          exact hmY
        · have hne : σ ‘ n ≠ σ ‘ a := fun h ↦
            haA ((injective_value_eq hσ.1 hσ.2.1 (hAω n hnA) haω h) ▸ hnA)
          rw [internalTransposition_fixed (function_value_mem hσ.1 (hAω _ hnA)) hne
            (hmimg n (mem_insert.mpr (Or.inr hnA)))]
          exact hmove n hnA
  exact (key X hX).2 hXω hXE

/-- Finite interpolation of an existing permutation while fixing a protected set. -/
theorem finite_permutation_extend_fixing {I E D π : V}
    (hEI : E ⊆ I) (hDI : D ⊆ I) (hD : IsInternallyFinite D)
    (hπ : IsInternalPermutation I π)
    (hfix : ∀ i ∈ D, i ∈ E → π ‘ i = i)
    (havoid : ∀ i ∈ D, i ∉ E → π ‘ i ∉ E) :
    ∃ σ, IsInternalPermutation I σ ∧ (∀ i ∈ E, σ ‘ i = i) ∧
      ∀ i ∈ D, σ ‘ i = π ‘ i := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  have hd : domain (π ↾ D) = D := by
    rw [domain_restrict_eq, domain_eq_of_mem_function hπ.1, inter_eq_right_of_subset hDI]
  have hr : range (π ↾ D) ⊆ I := by
    intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    exact range_subset_of_mem_function hπ.1 y
      (mem_range_iff.mpr ⟨x, (kpair_mem_restrict_iff.mp hxy).1⟩)
  have hf : π ↾ D ∈ I ^ D := by
    simpa only [hd] using mem_function_of_mem_function_of_subset
      (IsFunction.mem_function (π ↾ D)) hr
  have hi : Injective (π ↾ D) := fun x y z hx hy ↦
    hπ.2.1 x y z (kpair_mem_restrict_iff.mp hx).1 (kpair_mem_restrict_iff.mp hy).1
  have hv : ∀ i ∈ D, (π ↾ D) ‘ i = π ‘ i := fun i hi ↦
    value_restrict (by rw [domain_eq_of_mem_function hπ.1]; exact hDI i hi) hi
  obtain ⟨σ, hσ, hσfix, hagree⟩ := finite_injection_extend_fixing hEI hDI hD hf hi
    (fun i hi hE ↦ (hv i hi).trans (hfix i hi hE))
    (fun i hi hE ↦ by rw [hv i hi]; exact havoid i hi hE)
  exact ⟨σ, hσ, hσfix, fun i hi ↦ (hagree i hi).trans (hv i hi)⟩

/-- A finite injection into the naturals extends to a permutation. -/
theorem exists_internalPermutation_extending {E g : V} (hE : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (hg : g ∈ (ω : V) ^ E) (hinj : Injective g) :
    ∃ π, IsInternalPermutation (ω : V) π ∧ ∀ i ∈ E, π ‘ i = g ‘ i := by
  obtain ⟨π, hπ, _, hagree⟩ := finite_injection_extend_fixing
    (E := (∅ : V)) (fun _ hi ↦ (not_mem_empty hi).elim) hE hEf hg hinj
    (fun _ _ hi ↦ (not_mem_empty hi).elim) (fun _ _ _ ↦ not_mem_empty)
  exact ⟨π, hπ, hagree⟩

/-- Preserve the protected finite set while moving the remaining prescribed points. -/
theorem exists_internalPermutation_fixing_avoiding {e S T : V} (heω : e ⊆ (ω : V))
    (hSω : S ⊆ (ω : V)) (hef : IsInternallyFinite e) (hSf : IsInternallyFinite S)
    (hTf : IsInternallyFinite T) :
    ∃ π, IsInternalPermutation (ω : V) π ∧ (∀ i ∈ e, π ‘ i = i) ∧
      ∀ i ∈ S, i ∉ e → π ‘ i ∉ T := by
  let X : V := {i ∈ S ; i ∉ e}
  let Y : V := {i ∈ T ; i ∈ (ω : V)}
  have hXS : X ⊆ S := fun _ hi ↦ (mem_sep_iff.mp hi).1
  have hYT : Y ⊆ T := fun _ hi ↦ (mem_sep_iff.mp hi).1
  obtain ⟨π, hπ, hfix, hmove⟩ := exists_permutation_moving_fixing hef heω
    (internallyFinite_subset hSf hXS) (fun i hi ↦ hSω i (hXS i hi))
    (internallyFinite_subset hTf hYT) (fun _ hi ↦ (mem_sep_iff.mp hi).2)
    (fun _ hi ↦ (mem_sep_iff.mp hi).2)
  refine ⟨π, hπ, hfix, ?_⟩
  intro i hi hie hiT
  exact hmove i (mem_sep_iff.mpr ⟨hi, hie⟩)
    (mem_sep_iff.mpr ⟨hiT, function_value_mem hπ.1 (hSω i hi)⟩)

end ZFVP



