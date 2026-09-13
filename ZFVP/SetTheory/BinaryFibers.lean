import ZFVP.SetTheory.BinaryExpansionReals
import ZFVP.SetTheory.BinaryPrefixSeparation
import ZFVP.SetTheory.DedekindRealTopology
import ZFVP.SetTheory.FiniteSets

/-! Every fiber of the actual binary map has at most two members. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryReal_no_three_ordered {c d e : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (he : e ∈ cantorSpace V) (n : InternalNatural V)
    (hcd : InternalNatural.binaryNumeratorOf c hc n < InternalNatural.binaryNumeratorOf d hd n)
    (hde : InternalNatural.binaryNumeratorOf d hd n < InternalNatural.binaryNumeratorOf e he n)
    (hce : binaryReal c = binaryReal e) : False := by
  have hgap : InternalRational.binaryApprox c hc n + InternalRational.dyadic n <
      InternalRational.binaryApprox e he n :=
    lt_of_le_of_lt (InternalRational.binaryApprox_gap hc hd n hcd)
      (lt_of_lt_of_le (lt_add_of_pos_right _ (InternalRational.dyadic_pos n))
        (InternalRational.binaryApprox_gap hd he n hde))
  have hcuts : rationalCut (binaryValue e n.val) ⊆ rationalCut (binaryUpper c n.val) := by
    apply subset_trans (binaryReal_lower n.property)
    rw [← hce]
    exact binaryReal_upper hc n.property
  have hle : InternalRational.binaryApprox e he n ≤
      InternalRational.binaryApprox c hc n + InternalRational.dyadic n :=
    InternalRational.le_of_rationalCut_subset hcuts
  exact not_lt_of_ge hle hgap

theorem binaryNumerator_three_same_image {c d e : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (he : e ∈ cantorSpace V) (n : InternalNatural V)
    (hcd : binaryReal c = binaryReal d) (hce : binaryReal c = binaryReal e) :
    binaryNumerator c n.val = binaryNumerator d n.val ∨
      binaryNumerator c n.val = binaryNumerator e n.val ∨
        binaryNumerator d n.val = binaryNumerator e n.val := by
  let A := InternalNatural.binaryNumeratorOf c hc n
  let B := InternalNatural.binaryNumeratorOf d hd n
  let C := InternalNatural.binaryNumeratorOf e he n
  have hde := hcd.symm.trans hce
  rcases lt_trichotomy A B with hab | hab | hba
  · rcases lt_trichotomy B C with hbc | hbc | hcb
    · exact (binaryReal_no_three_ordered hc hd he n hab hbc hce).elim
    · exact Or.inr (Or.inr (congrArg Subtype.val hbc))
    · rcases lt_trichotomy A C with hac | hac | hca
      · exact (binaryReal_no_three_ordered hc he hd n hac hcb hcd).elim
      · exact Or.inr (Or.inl (congrArg Subtype.val hac))
      · exact (binaryReal_no_three_ordered he hc hd n hca hab hde.symm).elim
  · exact Or.inl (congrArg Subtype.val hab)
  · rcases lt_trichotomy A C with hac | hac | hca
    · exact (binaryReal_no_three_ordered hd hc he n hba hac hde).elim
    · exact Or.inr (Or.inl (congrArg Subtype.val hac))
    · rcases lt_trichotomy B C with hbc | hbc | hcb
      · exact (binaryReal_no_three_ordered hd he hc n hbc hca hcd.symm).elim
      · exact Or.inr (Or.inr (congrArg Subtype.val hbc))
      · exact (binaryReal_no_three_ordered he hd hc n hcb hba hce.symm).elim

theorem cantor_ne_coordinate {c d : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (hne : c ≠ d) : ∃ i ∈ (ω : V), c ‘ i ≠ d ‘ i := by
  by_contra h
  push Not at h
  have : IsFunction c := IsFunction.of_mem hc
  have : IsFunction d := IsFunction.of_mem hd
  apply hne
  apply functions_eq_of_domain_values (by rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function hd])
  intro i hi
  rw [domain_eq_of_mem_function hc] at hi
  exact h i hi

theorem binaryReal_fiber_at_most_two {c d e : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (he : e ∈ cantorSpace V)
    (hcd : binaryReal c = binaryReal d) (hce : binaryReal c = binaryReal e) :
    c = d ∨ c = e ∨ d = e := by
  by_contra h
  have hnecd : c ≠ d := fun hcd ↦ h (Or.inl hcd)
  have hnece : c ≠ e := fun hce ↦ h (Or.inr (Or.inl hce))
  have hnede : d ≠ e := fun hde ↦ h (Or.inr (Or.inr hde))
  obtain ⟨i, hi, hicd⟩ := cantor_ne_coordinate hc hd hnecd
  obtain ⟨j, hj, hjce⟩ := cantor_ne_coordinate hc he hnece
  obtain ⟨k, hk, hkde⟩ := cantor_ne_coordinate hd he hnede
  let I : InternalNatural V := ⟨i, hi⟩
  let J : InternalNatural V := ⟨j, hj⟩
  let K : InternalNatural V := ⟨k, hk⟩
  let n : InternalNatural V := max I (max J K) + 1
  have hin : i ∈ n.val := lt_of_le_of_lt (le_max_left I (max J K)) (lt_add_one _)
  have hjn : j ∈ n.val := lt_of_le_of_lt
    (le_trans (le_max_left J K) (le_max_right I (max J K))) (lt_add_one _)
  have hkn : k ∈ n.val := lt_of_le_of_lt
    (le_trans (le_max_right J K) (le_max_right I (max J K))) (lt_add_one _)
  rcases binaryNumerator_three_same_image hc hd he n hcd hce with hnum | hnum | hnum
  · exact hicd (binaryNumerator_agree_of_eq hc hd n.property hnum i hin)
  · exact hjce (binaryNumerator_agree_of_eq hc he n.property hnum j hjn)
  · exact hkde (binaryNumerator_agree_of_eq hd he n.property hnum k hkn)

noncomputable def binaryFiber (x : V) : V :=
  {c ∈ cantorSpace V ; binaryReal c = x}

theorem mem_binaryFiber_iff (x c : V) : c ∈ binaryFiber x ↔
    c ∈ cantorSpace V ∧ binaryReal c = x := by simp [binaryFiber]

instance binaryFiber_definable : ℒₛₑₜ-function₁[V] binaryFiber := by
  have h : ℒₛₑₜ-relation (fun F x : V ↦ ∀ c, c ∈ F ↔ c ∈ cantorSpace V ∧ binaryReal c = x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_binaryFiber_iff]

theorem binaryFiber_finite (x : V) : IsInternallyFinite (binaryFiber x) := by
  by_cases h : ∃ c, c ∈ binaryFiber x
  · obtain ⟨c, hc⟩ := h
    by_cases h' : ∃ d ∈ binaryFiber x, d ≠ c
    · obtain ⟨d, hd, hdc⟩ := h'
      apply internallyFinite_subset (internallyFinite_insert (internallyFinite_insert internallyFinite_empty c) d)
      intro e he
      obtain ⟨hcC, hcx⟩ := (mem_binaryFiber_iff _ _).mp hc
      obtain ⟨hdC, hdx⟩ := (mem_binaryFiber_iff _ _).mp hd
      obtain ⟨heC, hex⟩ := (mem_binaryFiber_iff _ _).mp he
      rcases binaryReal_fiber_at_most_two hcC hdC heC (hcx.trans hdx.symm) (hcx.trans hex.symm) with hcd | hce | hde
      · exact (hdc hcd.symm).elim
      · simp [← hce]
      · simp [← hde]
    · apply internallyFinite_subset (internallyFinite_insert internallyFinite_empty c)
      intro e he
      have hec : e = c := by by_contra hne; exact h' ⟨e, he, hne⟩
      simp [hec]
  · have he : binaryFiber x = ∅ := by
      apply mem_ext
      intro c
      simp only [not_mem_empty, iff_false]
      exact fun hc ↦ h ⟨c, hc⟩
    rw [he]
    exact internallyFinite_empty

end ZFVP
