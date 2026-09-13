import ZFVP.SetTheory.HODCantorTransport
import ZFVP.SetTheory.LevelCounting
import ZFVP.SetTheory.FiniteCardinalArithmetic
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.WellOrderedCardinal

/-! The regularity properties pass from `V` to the HOD class model: a set of reals of HOD which is
Lebesgue measurable, has the Baire property or has the perfect set property in `V` has the same
property inside HOD, because all witnesses are coded by reals and lie in HOD. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def openFromCodeFormula : SetTheorySemisentence 4 :=
  f“x S z P. x ∈ !cantorSpaceFormula ∧ ∃ s ∈ S, !restrict.dfn x (!domain.dfn s) = s”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_openFromCodeFormula (x S z P : V) :
    openFromCodeFormula.Evalb ![x, S, z, P] ↔ x ∈ cantorSpace V ∧ ∃ s ∈ S, x ↾ (domain s) = s := by
  simp [openFromCodeFormula]

section

variable (Pf : SetTheorySemisentence 2) (p : V)
  [Nonempty (HODDom Pf p)] [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (hreal : ∀ x ∈ cantorSpace V, IsAllowed Pf x p)
  (c e : V) (hc : c ∈ (ω : V) ^ binarySequences V) (hcinj : Injective c) (hcall : IsAllowed Pf c p)
  (he : e ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V))) (heinj : Injective e) (heall : IsAllowed Pf e p)

include hreal in
theorem isHOD_openFrom {S : V} (hS : IsHOD Pf S p) : IsHOD Pf (openFrom S) p := by
  refine isHOD_of_od Pf ?_ (fun x hx ↦ isHOD_of_real Pf p hreal ((mem_openFrom_iff S x).mp hx).1)
  refine isOD_of_two Pf openFromCodeFormula (IsHOD.od Pf hS) (isOD_empty Pf p)
    (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
  intro x
  rw [eval_openFromCodeFormula, mem_openFrom_iff]

include hreal hc hcinj hcall in
theorem val_powerBinarySequences :
    (℘ (binarySequences (HODDom Pf p))).val = ℘ (binarySequences V) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := exists_val_of_mem Pf p hy
    rw [mem_power_iff] at hz ⊢
    rw [← val_binarySequences Pf p]
    exact (subset_val_iff Pf p _ _).mpr hz
  · intro hy
    have hyB : y ⊆ binarySequences V := mem_power_iff.mp hy
    have hz : toHOD Pf p (isHOD_of_subset_binarySequences Pf p hreal c hc hcinj hcall hyB) ∈
        ℘ (binarySequences (HODDom Pf p)) := by
      rw [mem_power_iff, ← subset_val_iff Pf p, val_binarySequences Pf p]
      exact hyB
    exact hz

include hc hcinj hcall in
theorem smallMeasure_of_val {F m : HODDom Pf p} (hF : F ⊆ binarySequences (HODDom Pf p))
    (hm : m ∈ (ω : HODDom Pf p)) (h : SmallMeasure F.val m.val) : SmallMeasure F m := by
  obtain ⟨N, hN, hdom, g, hg, hginj⟩ := h
  have hm' : m.val ∈ (ω : V) := (mem_omega_val Pf p m).mp hm
  let N' : HODDom Pf p := toHOD Pf p (isHOD_natural Pf p hN)
  have hN' : N' ∈ (ω : HODDom Pf p) := (mem_omega_val Pf p N').mpr hN
  have hFB : F.val ⊆ binarySequences V := by
    rw [← val_binarySequences Pf p]
    exact (subset_val_iff Pf p _ _).mpr hF
  -- the injection is a finite set of pairs of finite sequences, hence lies in HOD
  have hgsub : g ⊆ (shadow F.val N ×ˢ (((2 : ℕ) : V) ^ m.val)) ×ˢ (((2 : ℕ) : V) ^ N) :=
    (mem_function_iff.mp hg).1
  have hgfin : IsInternallyFinite g :=
    internallyFinite_subset (internallyFinite_prod (internallyFinite_prod (shadow_finite hN)
      (internallyFinite_two_pow hm')) (internallyFinite_two_pow hN)) hgsub
  have hgHOD : IsHOD Pf g p := by
    refine isHOD_of_finite Pf p hgfin (fun q hq ↦ ?_)
    obtain ⟨st, hst, u, hu, rfl⟩ := mem_prod_iff.mp (hgsub q hq)
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_prod_iff.mp hst
    have hsB : s ∈ binarySequences V :=
      function_power_subset_binarySequences hN s (shadow_subset_power _ _ s hs)
    have htB : t ∈ binarySequences V := function_power_subset_binarySequences hm' t ht
    have huB : u ∈ binarySequences V := function_power_subset_binarySequences hN u hu
    exact isHOD_kpair Pf p (isHOD_kpair Pf p (isHOD_of_mem_binarySequences Pf p c hc hcinj hcall hsB)
      (isHOD_of_mem_binarySequences Pf p c hc hcinj hcall htB))
      (isHOD_of_mem_binarySequences Pf p c hc hcinj hcall huB)
  let g' : HODDom Pf p := toHOD Pf p hgHOD
  refine ⟨N', hN', fun s hs ↦ ?_, g', ?_, ?_⟩
  · have := hdom s.val hs
    rw [← val_domain Pf p] at this
    exact (subset_val_iff Pf p _ _).mp this
  · rw [mem_function_val Pf p, val_finitePower Pf p _ hN', val_prod Pf p, val_shadow Pf p F N' hN',
      val_finitePower Pf p _ hm, val_two Pf p]
    exact hg
  · exact (injective_val Pf p g').mp hginj

include hreal hc hcinj hcall he heinj heall in
theorem isNull_of_val {A : HODDom Pf p} (h : IsNull A.val) : IsNull A := by
  intro m hm
  obtain ⟨f, hf, hcov, hsmall⟩ := h m.val ((mem_omega_val Pf p m).mp hm)
  let f' : HODDom Pf p :=
    toHOD Pf p (isHOD_of_mem_function_binarySequences Pf p hreal c e hc hcinj hcall he heinj heall hf)
  have hf' : f' ∈ binarySequences (HODDom Pf p) ^ (ω : HODDom Pf p) := by
    rw [mem_function_val Pf p, val_binarySequences Pf p, val_omega Pf p]
    exact hf
  have hff : IsFunction f' := IsFunction.of_mem hf'
  have hfd : domain f' = (ω : HODDom Pf p) := domain_eq_of_mem_function hf'
  have hffV : IsFunction f := IsFunction.of_mem hf
  refine ⟨f', hf', fun x hx ↦ ?_, fun k hk ↦ ?_⟩
  · obtain ⟨i, hi, hxi⟩ := hcov x.val hx
    let i' : HODDom Pf p := toHOD Pf p (isHOD_natural Pf p hi)
    have hi' : i' ∈ (ω : HODDom Pf p) := (mem_omega_val Pf p i').mpr hi
    refine ⟨i', hi', val_injective Pf p ?_⟩
    rw [val_restrict Pf p, val_domain Pf p, val_value Pf p f' i' (by rw [hfd]; exact hi')]
    exact hxi
  · have hk' : k.val ∈ (ω : V) := (mem_omega_val Pf p k).mp hk
    refine smallMeasure_of_val Pf p c hc hcinj hcall ?_ hm ?_
    · intro y hy
      obtain ⟨q, hq, hqy⟩ := (mem_image_iff' _ _ _).mp hy
      have hqω : q ∈ (ω : HODDom Pf p) := IsTransitive.ω.mem_trans hq hk
      rw [← value_eq_of_kpair_mem hqy]
      exact function_value_mem hf' hqω
    · rw [val_image Pf p]
      exact hsmall k.val hk'

include hreal he heinj heall in
theorem isInternallyCountable_of_val {A : HODDom Pf p} (hA : A.val ⊆ cantorSpace V)
    (h : IsInternallyCountable A.val) : IsInternallyCountable A := by
  by_cases hemp : ∀ x, x ∉ A.val
  · have hA0 : A = ∅ := val_injective Pf p (by
      rw [val_empty Pf p]
      apply mem_ext
      intro x
      exact ⟨fun hx ↦ (hemp x hx).elim, fun hx ↦ (not_mem_empty hx).elim⟩)
    rw [hA0]
    exact cardLE_of_subset (empty_subset _)
  · push Not at hemp
    obtain ⟨x₀, hx₀⟩ := hemp
    obtain ⟨E, hE, hr⟩ := exists_surjection_of_cardLE h hx₀
    have hEc : E ∈ (cantorSpace V) ^ (ω : V) := mem_function_of_mem_function_of_subset hE hA
    let E' : HODDom Pf p := toHOD Pf p (isHOD_of_mem_function_cantorSpace Pf p hreal e he heinj heall hEc)
    have hE' : E' ∈ A ^ (ω : HODDom Pf p) := by
      rw [mem_function_val Pf p, val_omega Pf p]
      exact hE
    have hr' : range E' = A := val_injective Pf p (by rw [val_range Pf p]; exact hr)
    exact cardLE_of_surjective_function (ordinal_wellOrderable (ω : HODDom Pf p)) hE' hr'

include hreal c hc hcinj hcall he heinj heall in
/-- The perfect set property passes into HOD. -/
theorem perfectSetProperty_of_val {A : HODDom Pf p} (hA : A.val ⊆ cantorSpace V)
    (h : PerfectSetProperty A.val) : PerfectSetProperty A := by
  rcases h with hc' | ⟨T, hT, hTA⟩
  · exact Or.inl (isInternallyCountable_of_val Pf p hreal e he heinj heall hA hc')
  · right
    let T' : HODDom Pf p := toHOD Pf p (isHOD_of_subset_binarySequences Pf p hreal c hc hcinj hcall hT.1.1)
    refine ⟨T', (isPerfectTree_val Pf p T').mpr hT, ?_⟩
    rw [← subset_val_iff Pf p, val_treeBody Pf p hreal]
    exact hTA

include hreal c hc hcinj hcall in
theorem isOpen_of_val {U : HODDom Pf p} (h : IsOpen U.val) : IsOpen U := by
  obtain ⟨S, hS, hU⟩ := h
  let S' : HODDom Pf p := toHOD Pf p (isHOD_of_subset_binarySequences Pf p hreal c hc hcinj hcall hS)
  refine ⟨S', ?_, val_injective Pf p ?_⟩
  · rw [← subset_val_iff Pf p, val_binarySequences Pf p]
    exact hS
  · rw [val_openFrom Pf p hreal]
    exact hU

include hreal hc hcinj hcall he heinj heall in
theorem isMeagre_of_val {A : HODDom Pf p} (h : IsMeagre A.val) : IsMeagre A := by
  obtain ⟨f, hf, hnd, hcov⟩ := h
  let f' : HODDom Pf p := toHOD Pf p
    (isHOD_of_mem_function_power_binarySequences Pf p hreal c e hc hcinj hcall he heinj heall hf)
  have hf' : f' ∈ (℘ (binarySequences (HODDom Pf p))) ^ (ω : HODDom Pf p) := by
    rw [mem_function_val Pf p, val_powerBinarySequences Pf p hreal c hc hcinj hcall, val_omega Pf p]
    exact hf
  have hff : IsFunction f' := IsFunction.of_mem hf'
  have hfd : domain f' = (ω : HODDom Pf p) := domain_eq_of_mem_function hf'
  refine ⟨f', hf', fun n hn ↦ ?_, fun x hx ↦ ?_⟩
  · rw [isNowhereDenseTree_val Pf p, val_value Pf p f' n (by rw [hfd]; exact hn)]
    exact hnd n.val ((mem_omega_val Pf p n).mp hn)
  · obtain ⟨n, hn, hxn⟩ := hcov x.val hx
    let n' : HODDom Pf p := toHOD Pf p (isHOD_natural Pf p hn)
    have hn' : n' ∈ (ω : HODDom Pf p) := (mem_omega_val Pf p n').mpr hn
    refine ⟨n', hn', ?_⟩
    rw [← mem_val_iff, val_treeBody Pf p hreal, val_value Pf p f' n' (by rw [hfd]; exact hn')]
    exact hxn

include hreal hc hcinj hcall he heinj heall in
/-- The Baire property passes into HOD. -/
theorem baireProperty_of_val {A : HODDom Pf p} (h : BaireProperty A.val) : BaireProperty A := by
  obtain ⟨U, hU, hmeagre⟩ := h
  obtain ⟨S, hS, rfl⟩ := hU
  let U' : HODDom Pf p := toHOD Pf p (isHOD_openFrom Pf p hreal
    (isHOD_of_subset_binarySequences Pf p hreal c hc hcinj hcall hS))
  refine ⟨U', isOpen_of_val Pf p hreal c hc hcinj hcall ⟨S, hS, rfl⟩, ?_⟩
  apply isMeagre_of_val Pf p hreal c e hc hcinj hcall he heinj heall
  rw [val_union Pf p, val_sdiff Pf p, val_sdiff Pf p]
  exact hmeagre

include hreal hc hcinj hcall he heinj heall in
/-- Lebesgue measurability passes into HOD. -/
theorem isLebesgueMeasurable_of_val {A : HODDom Pf p} (h : IsLebesgueMeasurable A.val) :
    IsLebesgueMeasurable A := by
  obtain ⟨g, hg, hAg, hnull⟩ := h
  let g' : HODDom Pf p := toHOD Pf p
    (isHOD_of_mem_function_power_binarySequences Pf p hreal c e hc hcinj hcall he heinj heall hg)
  have hg' : g' ∈ (℘ (binarySequences (HODDom Pf p))) ^ (ω : HODDom Pf p) := by
    rw [mem_function_val Pf p, val_powerBinarySequences Pf p hreal c hc hcinj hcall, val_omega Pf p]
    exact hg
  refine ⟨g', hg', ?_, ?_⟩
  · rw [← subset_val_iff Pf p, val_gDelta Pf p hreal hg']
    exact hAg
  · apply isNull_of_val Pf p hreal c e hc hcinj hcall he heinj heall
    rw [val_sdiff Pf p, val_gDelta Pf p hreal hg']
    exact hnull

end

end ZFVP
