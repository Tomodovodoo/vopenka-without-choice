import ZFVP.SetTheory.DependentChoicePathUnions
import ZFVP.SetTheory.LeastDependentChoiceFailure
import ZFVP.SetTheory.FiniteCofinality

/-! Dependent choice at a limit follows from its shorter instances and
the instance at its cofinality. Hence the least failure is regular. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoiceAt_of_cofinality {κ : V} [IsOrdinal κ]
    (hzero : (0 : V) ∈ κ) (hsucc : ∀ α ∈ κ, succ α ∈ κ)
    (hbelow : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hcf : InternalDependentChoiceAt (internalCofinality κ)) : InternalDependentChoiceAt κ := by
  intro A R hA hR
  obtain ⟨g, hg⟩ := cofinalMap_exists κ
  let P := dependentChoicePaths κ A R
  have hP (s : V) : s ∈ P ↔ domain s ∈ κ ∧ IsDependentChoicePath A R (domain s) s :=
    mem_dependentChoicePaths κ A R s
  have hempty : (∅ : V) ∈ P := (hP ∅).mpr
    ⟨by simpa [zero_def] using hzero, by simpa using dependentChoicePath_empty A R⟩
  have hPf (s : V) (hs : s ∈ P) : IsFunction s := IsFunction.of_mem ((hP s).mp hs).2.1
  let Q : V := {z ∈ shorterSequences (internalCofinality κ) P ×ˢ P ;
    CompatibleFunctionFamily (range (kpair.π₁ z)) →
      ⋃ˢ range (kpair.π₁ z) ⊆ kpair.π₂ z ∧
      g ‘ (domain (kpair.π₁ z)) ∈ domain (kpair.π₂ z)}
  have hQ (s t : V) : ⟨s, t⟩ₖ ∈ Q ↔
      s ∈ shorterSequences (internalCofinality κ) P ∧ t ∈ P ∧
      (CompatibleFunctionFamily (range s) → ⋃ˢ range s ⊆ t ∧ g ‘ (domain s) ∈ domain t) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences (internalCofinality κ) P,
      ∃ t ∈ P, ⟨s, t⟩ₖ ∈ Q := by
    intro s hs
    obtain ⟨i, hi, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    by_cases hC : CompatibleFunctionFamily (range s)
    · have hu := dependentChoicePaths_union_bounded hi hsf hC
      have hu' := (hP _).mp hu
      let := IsOrdinal.of_mem hu'.1
      have hgi := function_value_mem hg.1 hi
      let := IsOrdinal.of_mem hgi
      let α := domain (⋃ˢ range s) ∪ succ (g ‘ i)
      let := ordinal_union_ordinal (domain (⋃ˢ range s)) (succ (g ‘ i))
      have hα : α ∈ κ := ordinal_union_mem hu'.1 (hsucc _ hgi)
      obtain ⟨t, ht, hut⟩ := dependentChoicePath_extend (hbelow α hα)
        (IsOrdinal.toIsTransitive.transitive _ hα) (subset_union_left _ _) hA hR hu'.2
      have htP : t ∈ P := (hP t).mpr (by
        rw [domain_eq_of_mem_function ht.1]
        exact ⟨hα, ht⟩)
      refine ⟨t, htP, (hQ s t).mpr ⟨hs, htP, fun _ ↦ ⟨hut, ?_⟩⟩⟩
      rw [domain_eq_of_mem_function hsf, domain_eq_of_mem_function ht.1]
      exact mem_union_iff.mpr (Or.inr (by simp))
    · exact ⟨∅, hempty, (hQ s ∅).mpr ⟨hs, hempty, fun hc ↦ False.elim (hC hc)⟩⟩
  obtain ⟨H, hH, hstep⟩ := hcf P Q ⟨∅, hempty⟩ hserial
  let := IsFunction.of_mem hH
  have hvalue (i : V) (hi : i ∈ internalCofinality κ) :
      domain (H ‘ i) ∈ κ ∧ IsDependentChoicePath A R (domain (H ‘ i)) (H ‘ i) :=
    (hP _).mp (function_value_mem hH hi)
  have hprogress : ∀ i : Ordinal V, i.val ∈ internalCofinality κ →
      (∀ j ∈ i.val, H ‘ j ⊆ H ‘ i.val) ∧ g ‘ i.val ∈ domain (H ‘ i.val) := by
    apply transfinite_induction (fun i ↦ i ∈ internalCofinality κ →
      (∀ j ∈ i, H ‘ j ⊆ H ‘ i) ∧ g ‘ i ∈ domain (H ‘ i)) (by definability)
    intro i ih hi
    have hisub : i.val ⊆ internalCofinality κ := IsOrdinal.toIsTransitive.transitive _ hi
    have hHi := function_restrict_mem hH hisub
    have hC : CompatibleFunctionFamily (range (H ↾ i.val)) :=
      compatible_range_of_increasing hHi hPf (by
        intro j hj k hk
        have hjcf := hisub j hj
        have hkcf := hisub k (IsOrdinal.toIsTransitive.mem_trans hk hj)
        let := IsOrdinal.of_mem hj
        rw [value_restrict (by rw [domain_eq_of_mem_function hH]; exact hkcf)
          (IsOrdinal.toIsTransitive.mem_trans hk hj),
          value_restrict (by rw [domain_eq_of_mem_function hH]; exact hjcf) hj]
        exact (ih (IsOrdinal.toOrdinal j) hj hjcf).1 k hk)
    have hh := ((hQ _ _).mp (hstep i.val hi)).2.2 hC
    rw [domain_eq_of_mem_function hHi] at hh
    refine ⟨?_, hh.2⟩
    intro j hj
    have hmem : H ‘ j ∈ range (H ↾ i.val) := mem_range_of_kpair_mem
      (kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (by
        rw [domain_eq_of_mem_function hH]; exact hisub j hj), hj⟩)
    exact subset_trans (subset_sUnion_of_mem hmem) hh.1
  have hinc : ∀ i ∈ internalCofinality κ, ∀ j ∈ i, H ‘ j ⊆ H ‘ i := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact (hprogress (IsOrdinal.toOrdinal i) hi).1
  have hC := compatible_range_of_increasing hH hPf hinc
  obtain ⟨hord, hpath⟩ := dependentChoicePath_union (A := A) (R := R) (by
    intro s hs
    have hh := (hP s).mp (range_subset_of_mem_function hH s hs)
    exact ⟨IsOrdinal.of_mem hh.1, hh.2⟩) hC
  have hd : domain (⋃ˢ range H) = κ := by
    apply SetTheory.subset_antisymm
    · intro β hβ
      obtain ⟨s, hs, hβs⟩ := (mem_domain_sUnion_iff _ _).mp hβ
      exact IsOrdinal.toIsTransitive.mem_trans hβs
        ((hP s).mp (range_subset_of_mem_function hH s hs)).1
    · intro β hβ
      let := IsOrdinal.of_mem hβ
      obtain ⟨i, hi, hβi⟩ := hg.2 β hβ
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem (function_value_mem hg.1 hi)
      let := IsOrdinal.of_mem (hvalue i hi).1
      have hcover := (hprogress (IsOrdinal.toOrdinal i) hi).2
      have hmem : H ‘ i ∈ range H := mem_range_of_kpair_mem (kpair_value_mem (by
        rw [domain_eq_of_mem_function hH]; exact hi))
      exact (mem_domain_sUnion_iff _ _).mpr
        ⟨H ‘ i, hmem, ordinal_mem_of_subset_mem hβi hcover⟩
  rw [hd] at hpath
  exact ⟨⋃ˢ range H, hpath⟩

theorem IsLeastDependentChoiceFailure.cofinality {κ : V} (hκ : IsLeastDependentChoiceFailure κ) :
    internalCofinality κ = κ := by
  let := hκ.1
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
  · exact he
  · apply False.elim
    apply hκ.2.1
    exact dependentChoiceAt_of_cofinality
      (hκ.omega_subset _ (by simp)) hκ.successor_closed
      (fun α hα ↦ hκ.below hα) (hκ.below hlt)

theorem IsLeastDependentChoiceFailure.regular {κ : V} (hκ : IsLeastDependentChoiceFailure κ) :
    IsRegularCardinal κ := by
  let := hκ.1
  refine ⟨?_, hκ.omega_subset, hκ.cofinality⟩
  exact hκ.cofinality ▸ internalCofinality_initial κ

theorem leastDependentChoiceFailure_existsRegular (hAC : ¬InternalChoice V) :
    ∃ κ : V, IsLeastDependentChoiceFailure κ ∧ IsRegularCardinal κ := by
  obtain ⟨κ, hκ, _⟩ := leastDependentChoiceFailure_existsUnique hAC
  exact ⟨κ, hκ, hκ.regular⟩

end ZFVP
