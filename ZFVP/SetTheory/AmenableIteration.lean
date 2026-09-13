import ZFVP.SetTheory.AmenableReplacement
import ZFVP.SetTheory.PathDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An internally finite initial segment of iteration. -/
def IsIterationTrace (F : V → V) (a n f : V) : Prop :=
  IsFunction f ∧ domain f = succ n ∧ f ‘ (0 : V) = a ∧
    ∀ i ∈ n, f ‘ (succ i) = F (f ‘ i)

theorem iterationTrace_definable {X : V → Prop} (F : V → V)
    (hF : PredicateExpansion.Fun X F) (a : V) :
    PredicateExpansion.Rel X (IsIterationTrace F a) := by
  let : Structure predicateLanguage V := predicateExpansion X
  have hgraph : Language.DefinableRel predicateLanguage (fun y x : V ↦ y = F x) := hF
  change Language.DefinableRel predicateLanguage (IsIterationTrace F a)
  unfold IsIterationTrace
  relative_definability X

theorem iterationTrace_zero (F : V → V) (a : V) : ∃ f, IsIterationTrace F a 0 f := by
  let f := definableGraph (succ (0 : V)) (fun _ ↦ a) (by definability)
  refine ⟨f, inferInstance, domain_definableGraph _ _ _, ?_, ?_⟩
  · exact value_definableGraph _ _ _ (by simp)
  · intro i hi
    exact False.elim (not_mem_empty hi)

theorem IsIterationTrace.extend {F : V → V} {a n f : V}
    (hn : n ∈ (ω : V)) (hf : IsIterationTrace F a n f) :
    ∃ g, IsIterationTrace F a (succ n) g := by
  have : IsFunction f := hf.1
  let x := F (f ‘ n)
  let A := insert x (range f)
  have hfm : f ∈ A ^ succ n :=
    mem_function_of_mem_function_of_subset (by simpa only [hf.2.1] using (isFunction_iff.mp hf.1))
      (fun z hz ↦ mem_insert.mpr (Or.inr hz))
  have hx : x ∈ A := mem_insert.mpr (Or.inl rfl)
  let g := insert ⟨succ n, x⟩ₖ f
  have hgm := function_append_mem hfm hx
  refine ⟨g, IsFunction.of_mem hgm, domain_eq_of_mem_function hgm, ?_, ?_⟩
  · exact (function_append_value_old hfm hx (zero_mem_succ_natural hn)).trans hf.2.2.1
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [function_append_value_new hfm hx, function_append_value_old hfm hx (by simp)]
    · rw [function_append_value_old hfm hx (succ_mem_succ_of_natural_mem hn hi),
        function_append_value_old hfm hx (mem_succ_iff.mpr (Or.inr hi))]
      exact hf.2.2.2 i hi

theorem IsIterationTrace.agree {F : V → V} {a n m f g : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hf : IsIterationTrace F a n f) (hg : IsIterationTrace F a m g) :
    ∀ k ∈ (ω : V), k ∈ succ n → k ∈ succ m → f ‘ k = g ‘ k := by
  apply naturalNumber_induction (fun k ↦ k ∈ succ n → k ∈ succ m → f ‘ k = g ‘ k)
    (by definability)
  · intro _ _
    exact hf.2.2.1.trans hg.2.2.1.symm
  · intro k hk ih hkn hkm
    have pre (t : V) (ht : t ∈ (ω : V)) (hs : succ k ∈ succ t) : k ∈ t := by
      have : IsOrdinal t := IsOrdinal.of_mem ht
      rcases mem_succ_iff.mp hs with he | hh
      · exact he ▸ mem_succ_self k
      · exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hh
    have hk'n := pre n hn hkn
    have hk'm := pre m hm hkm
    rw [hf.2.2.2 k hk'n, hg.2.2.2 k hk'm,
      ih (mem_succ_iff.mpr (Or.inr hk'n)) (mem_succ_iff.mpr (Or.inr hk'm))]

theorem IsIterationTrace.unique {F : V → V} {a n f g : V}
    (hn : n ∈ (ω : V)) (hf : IsIterationTrace F a n f) (hg : IsIterationTrace F a n g) : f = g := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  apply functions_eq_of_domain_values (hf.2.1.trans hg.2.1.symm)
  intro k hk
  rw [hf.2.1] at hk
  exact hf.agree hn hn hg k (IsTransitive.ω.mem_trans hk (ω_succ_closed hn)) hk hk

namespace IsAmenablePredicate
variable {X : V → Prop} (hX : IsAmenablePredicate X)
include hX

theorem iterationTrace_exists (F : V → V) (hF : PredicateExpansion.Fun X F) (a : V) :
    ∀ n ∈ (ω : V), ∃ f, IsIterationTrace F a n f := by
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinableRel predicateLanguage (IsIterationTrace F a) := iterationTrace_definable F hF a
  have hP : PredicateExpansion.Pred X (fun n ↦ ∃ f, IsIterationTrace F a n f) := by
    change Language.DefinablePred predicateLanguage (fun n : V ↦ ∃ f, IsIterationTrace F a n f)
    apply Language.Definable.exs
    exact Language.Definable.retraction (iterationTrace_definable F hF a) ![1, 0]
  apply hX.naturalInduction _ hP (iterationTrace_zero F a)
  intro n hn hh
  obtain ⟨f, hf⟩ := hh
  exact hf.extend hn

/-- A single internal graph contains the iterates at every internal natural,
including nonstandard indices. Replacement collects the unique finite traces. -/
theorem iterationGraph_exists (F : V → V) (hF : PredicateExpansion.Fun X F) (a : V) :
    ∃ g : V, IsFunction g ∧ domain g = (ω : V) ∧ g ‘ (0 : V) = a ∧
      ∀ n ∈ (ω : V), g ‘ (succ n) = F (g ‘ n) := by
  have hex := hX.iterationTrace_exists F hF a
  obtain ⟨C, hC⟩ := hX.replacementOn (ω : V) (IsIterationTrace F a)
    (iterationTrace_definable F hF a) (fun n hn ↦ by
      obtain ⟨f, hf⟩ := hex n hn
      exact ⟨f, hf, fun g hg ↦ hg.unique hn hf⟩)
  have hfunc : ∀ f ∈ C, IsFunction f := by
    intro f hf
    obtain ⟨n, _, hn⟩ := (hC f).mp hf
    exact hn.1
  have hcompat : CompatibleFunctionFamily C := by
    intro f hf g hg x y z hxy hxz
    obtain ⟨n, hn, hfn⟩ := (hC f).mp hf
    obtain ⟨m, hm, hgm⟩ := (hC g).mp hg
    have : IsFunction f := hfn.1
    have : IsFunction g := hgm.1
    have hxn : x ∈ succ n := hfn.2.1 ▸ mem_domain_of_kpair_mem hxy
    have hxm : x ∈ succ m := hgm.2.1 ▸ mem_domain_of_kpair_mem hxz
    exact (value_eq_of_kpair_mem hxy).symm.trans
      ((hfn.agree hn hm hgm x (IsTransitive.ω.mem_trans hxn (ω_succ_closed hn)) hxn hxm).trans
        (value_eq_of_kpair_mem hxz))
  let g := ⋃ˢ C
  have hgfun : IsFunction g := isFunction_sUnion hfunc hcompat
  have hdom : domain g = (ω : V) := by
    apply mem_ext
    intro n
    rw [mem_domain_sUnion_iff]
    constructor
    · rintro ⟨f, hf, hnf⟩
      obtain ⟨k, hk, hfk⟩ := (hC f).mp hf
      rw [hfk.2.1] at hnf
      exact IsTransitive.ω.mem_trans hnf (ω_succ_closed hk)
    · intro hn
      obtain ⟨f, hf⟩ := hex n hn
      exact ⟨f, (hC f).mpr ⟨n, hn, hf⟩, by rw [hf.2.1]; simp⟩
  refine ⟨g, hgfun, hdom, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := hex 0 (by simp)
    rw [value_sUnion_of_mem hfunc hcompat ((hC f).mpr ⟨0, by simp, hf⟩) (by rw [hf.2.1]; simp)]
    exact hf.2.2.1
  · intro n hn
    obtain ⟨f, hf⟩ := hex (succ n) (ω_succ_closed hn)
    have hfC := (hC f).mpr ⟨succ n, ω_succ_closed hn, hf⟩
    rw [value_sUnion_of_mem hfunc hcompat hfC (by rw [hf.2.1]; simp),
      value_sUnion_of_mem hfunc hcompat hfC (by rw [hf.2.1]; exact mem_succ_iff.mpr (Or.inr (by simp)))]
    exact hf.2.2.2 n (by simp)
end IsAmenablePredicate
end ZFVP
