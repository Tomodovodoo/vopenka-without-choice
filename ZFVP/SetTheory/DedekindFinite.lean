import ZFVP.SetTheory.InfiniteDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternallyDedekindFinite (A : V) : Prop := ∀ f ∈ A ^ A, Injective f → range f = A

instance isInternallyDedekindFinite_definable : ℒₛₑₜ-predicate[V] IsInternallyDedekindFinite := by
  unfold IsInternallyDedekindFinite
  definability

noncomputable def shiftCountableImage (f x : V) : V := by
  classical
  exact if x ∈ range f then f ‘ (succ ((converseGraph f) ‘ x)) else x

instance shiftCountableImage_definable : ℒₛₑₜ-function₂[V] shiftCountableImage := by
  have h : ℒₛₑₜ-relation₃ (fun y f x : V ↦
    (x ∈ range f ∧ y = f ‘ (succ ((converseGraph f) ‘ x))) ∨ (x ∉ range f ∧ y = x)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = shiftCountableImage (v 1) (v 2) ↔ _
  unfold shiftCountableImage
  split <;> simp_all

theorem not_dedekindFinite_of_omega_cardLE {A : V} (h : (ω : V) ≤# A) :
    ¬IsInternallyDedekindFinite A := by
  classical
  obtain ⟨f, hf, hfi⟩ := h
  let F := shiftCountableImage f
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hinv (x : V) (hx : x ∈ range f) : (converseGraph f) ‘ x ∈ (ω : V) :=
    function_value_mem (converseGraph_mem_function hf hfi) hx
  have hr (x : V) (hx : x ∈ range f) : F x = f ‘ (succ ((converseGraph f) ‘ x)) := by
    simp [F, shiftCountableImage, hx]
  have hn (x : V) (hx : x ∉ range f) : F x = x := by simp [F, shiftCountableImage, hx]
  have hm (x : V) (hx : x ∈ range f) : F x ∈ range f := by
    rw [hr x hx]
    exact value_mem_range hf (ω_succ_closed (hinv x hx))
  have hmaps (x : V) (hx : x ∈ A) : F x ∈ A := by
    by_cases hxr : x ∈ range f
    · exact range_subset_of_mem_function hf _ (hm x hxr)
    · rw [hn x hxr]
      exact hx
  have hinjective (x y : V) (heq : F x = F y) : x = y := by
    by_cases hx : x ∈ range f <;> by_cases hy : y ∈ range f
    · have hxω := hinv x hx
      have hyω := hinv y hy
      have hs : succ ((converseGraph f) ‘ x) = succ ((converseGraph f) ‘ y) :=
        injective_value_eq hf hfi (ω_succ_closed hxω) (ω_succ_closed hyω)
          ((hr x hx).symm.trans (heq.trans (hr y hy)))
      have : IsOrdinal ((converseGraph f) ‘ x) := IsOrdinal.of_mem hxω
      have : IsOrdinal ((converseGraph f) ‘ y) := IsOrdinal.of_mem hyω
      have hi : (converseGraph f) ‘ x = (converseGraph f) ‘ y := by
        simpa only [sUnion_succ_of_transitive] using congrArg (fun z : V ↦ ⋃ˢ z) hs
      exact (value_converseGraph_value hf hfi hx).symm.trans
        ((congrArg (fun z ↦ f ‘ z) hi).trans (value_converseGraph_value hf hfi hy))
    · exact False.elim (hy ((heq.trans (hn y hy)) ▸ hm x hx))
    · exact False.elim (hx ((heq.symm.trans (hn x hx)) ▸ hm y hy))
    · exact (hn x hx).symm.trans (heq.trans (hn y hy))
  have hmiss (x : V) : F x ≠ f ‘ 0 := by
    intro heq
    by_cases hx : x ∈ range f
    · have hs : succ ((converseGraph f) ‘ x) = (0 : V) :=
        injective_value_eq hf hfi (ω_succ_closed (hinv x hx)) (by simp) ((hr x hx).symm.trans heq)
      have hh : (converseGraph f) ‘ x ∈ succ ((converseGraph f) ‘ x) := by simp
      rw [hs] at hh
      exact not_mem_empty hh
    · exact hx (((hn x hx).symm.trans heq).symm ▸ value_mem_range hf (show (0 : V) ∈ ω by simp))
  let g := definableGraph A F hF
  have hg : g ∈ A ^ A := definableGraph_mem_function_of_mapsTo _ _ _ _ hmaps
  have hgi : Injective g := by
    intro x y z hx hy
    have hx' := (pair_mem_definableGraph_iff A F hF x z).mp hx
    have hy' := (pair_mem_definableGraph_iff A F hF y z).mp hy
    exact hinjective x y (hx'.2.symm.trans hy'.2)
  intro hd
  have h0 : f ‘ 0 ∈ range g := (hd g hg hgi).symm ▸ function_value_mem hf (show (0 : V) ∈ ω by simp)
  obtain ⟨x, hx⟩ := mem_range_iff.mp h0
  exact hmiss x ((pair_mem_definableGraph_iff A F hF x (f ‘ 0)).mp hx).2.symm

theorem omega_cardLE_of_not_dedekindFinite {A : V} (h : ¬IsInternallyDedekindFinite A) :
    (ω : V) ≤# A := by
  classical
  obtain ⟨g, hg, hgi, hgr⟩ : ∃ g ∈ A ^ A, Injective g ∧ range g ≠ A := by
    by_contra hn
    apply h
    intro g hg hi
    by_contra hr
    exact hn ⟨g, hg, hi, hr⟩
  obtain ⟨a, ha, har⟩ : ∃ a ∈ A, a ∉ range g := by
    by_contra hn
    apply hgr
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hg)
    intro x hx
    by_contra hxr
    exact hn ⟨x, hx, hxr⟩
  let F : V → V := fun x ↦ g ‘ x
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let b := naturalIteration F hF a
  have hbdef : ℒₛₑₜ-function₁ b := naturalIteration_definable F hF a
  have hb (n : V) (hn : n ∈ (ω : V)) : b n ∈ A :=
    naturalIteration_invariant F hF a (fun x ↦ x ∈ A) (by definability) ha
      (fun x hx ↦ function_value_mem hg hx) n hn
  have hzero : b 0 = a := naturalIteration_zero F hF a
  have hsucc (n : V) (hn : n ∈ (ω : V)) : b (succ n) = g ‘ (b n) := naturalIteration_succ F hF a hn
  have hdistinct : ∀ n ∈ (ω : V), ∀ m ∈ n, b m ≠ b n := by
    apply naturalNumber_induction (fun n ↦ ∀ m ∈ n, b m ≠ b n) (by definability)
    · intro m hm
      simp [zero_def] at hm
    · intro n hn ih m hm heq
      have hmω : m ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hm (ω_succ_closed hn)
      rcases internalNatural_cases hmω with h0 | ⟨k, hk, hmk⟩
      · rw [h0, hzero, hsucc n hn] at heq
        exact har (heq.symm ▸ value_mem_range hg (hb n hn))
      · have : IsOrdinal k := IsOrdinal.of_mem hk
        have hkn : k ∈ n := by
          have hne : m ≠ (0 : V) := by
            intro h
            have hh : k ∈ m := hmk.symm ▸ (show k ∈ succ k by simp)
            rw [h] at hh
            exact not_mem_empty hh
          have hh := natural_predecessor_mem hn hm hne
          simpa only [hmk, sUnion_succ_of_transitive] using hh
        rw [hmk, hsucc k hk, hsucc n hn] at heq
        exact ih k hkn (injective_value_eq hg hgi (hb k hk) (hb n hn) heq)
  let f := definableGraph (ω : V) b hbdef
  have hf : f ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ hb
  refine ⟨f, hf, ?_⟩
  intro n m z hnz hmz
  obtain ⟨hn, hzn⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef n z).mp hnz
  obtain ⟨hm, hzm⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef m z).mp hmz
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have heq : b n = b m := hzn.symm.trans hzm
  rcases IsOrdinal.mem_trichotomy n m with hlt | he | hgt
  · exact False.elim (hdistinct m hm n hlt heq)
  · exact he
  · exact False.elim (hdistinct n hn m hgt heq.symm)

theorem dedekindFinite_iff_no_omega_injection (A : V) :
    IsInternallyDedekindFinite A ↔ ¬(ω : V) ≤# A := by
  constructor
  · intro h hi
    exact not_dedekindFinite_of_omega_cardLE hi h
  · intro h
    by_contra hn
    exact h (omega_cardLE_of_not_dedekindFinite hn)

theorem not_dependentChoice_of_infinite_dedekindFinite {A : V}
    (hi : IsInternallyInfinite A) (hd : IsInternallyDedekindFinite A) : ¬InternalDependentChoice V :=
  not_dependentChoice_of_infinite_no_omega_injection hi ((dedekindFinite_iff_no_omega_injection A).mp hd)

theorem not_internalChoice_of_infinite_dedekindFinite {A : V}
    (hi : IsInternallyInfinite A) (hd : IsInternallyDedekindFinite A) : ¬InternalChoice V :=
  fun hAC ↦ not_dependentChoice_of_infinite_dedekindFinite hi hd (dependentChoice_of_internalChoice hAC)

end ZFVP
