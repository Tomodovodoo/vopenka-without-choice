import ZFVP.SetTheory.BaireRunRegularity
import ZFVP.SetTheory.PerfectTreeBranches

/-! The perfect-set property transfers to Baire space in arbitrary internal ZF models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem baireRunTreePreimage_perfect {T : V} (hT : IsPerfectTree T)
    (hD : treeBody T ⊆ cantorInfiniteOnes V) : IsPerfectBaireTree (baireRunTreePreimage T) := by
  refine ⟨baireRunTreePreimage_isTree hT.1, ?_, ?_⟩
  · apply (mem_baireRunTreePreimage_iff T ∅).mpr
    refine ⟨empty_mem_finiteSequences _, ?_⟩
    have hdom : domain (∅ : V) = 0 := by simp [zero_def]
    rw [baireFiniteRunCode, hdom, baireRunPrefix_zero]
    exact hT.2.1
  · intro s hs
    obtain ⟨hsn, hsT⟩ := (mem_baireRunTreePreimage_iff T s).mp hs
    obtain ⟨t, ht, u, hu, hst, hsu, hinc⟩ := hT.2.2 _ hsT
    obtain ⟨x, hxT, htx⟩ := perfectTree_branch_through hT ht
    obtain ⟨y, hyT, huy⟩ := perfectTree_branch_through hT hu
    let a := cantorRunDecode x
    let b := cantorRunDecode y
    have ha : a ∈ baireSpace V := cantorRunDecode_mem (hD x hxT)
    have hb : b ∈ baireSpace V := cantorRunDecode_mem (hD y hyT)
    have hea : baireRunCode a = x := baireRunCode_decode (hD x hxT)
    have heb : baireRunCode b = y := baireRunCode_decode (hD y hyT)
    have hta : t ⊆ baireRunCode a := by rw [hea]; exact htx
    have hub : u ⊆ baireRunCode b := by rw [heb]; exact huy
    have hsa := baireFiniteRunCode_reflects_subset hsn ha (subset_trans hst hta)
    have hsb := baireFiniteRunCode_reflects_subset hsn hb (subset_trans hsu hub)
    have : IsFunction a := IsFunction.of_mem ha
    have : IsFunction b := IsFunction.of_mem hb
    have : IsFunction t := binarySequence_isFunction (hT.1.1 t ht)
    have : IsFunction u := binarySequence_isFunction (hT.1.1 u hu)
    have : IsFunction (baireRunCode a) := baireRunCode_isFunction ha
    have hab : a ≠ b := by
      intro he
      have hua : u ⊆ baireRunCode a := by rw [he]; exact hub
      exact not_incompatible_of_subset_subset hta hua hinc
    have hex : ∃ i ∈ (ω : V), a ‘ i ≠ b ‘ i := by
      by_contra hnone
      apply hab
      apply functions_eq_of_domain_values (by rw [domain_eq_of_mem_function ha, domain_eq_of_mem_function hb])
      intro i hi
      rw [domain_eq_of_mem_function ha] at hi
      by_contra hne
      exact hnone ⟨i, hi, hne⟩
    obtain ⟨i, hi, hne⟩ := hex
    obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hsn
    have : IsFunction s := IsFunction.of_mem hsf
    let n := domain s ∪ succ i
    have hn : n ∈ (ω : V) := ordinal_union_mem hm (ω_succ_closed hi)
    have hin : i ∈ n := mem_union_iff.mpr (Or.inr (mem_succ_self i))
    have hav := function_restrict_mem ha (IsTransitive.transitive _ hn)
    have hbw := function_restrict_mem hb (IsTransitive.transitive _ hn)
    have : IsFunction (a ↾ n) := IsFunction.of_mem hav
    have : IsFunction (b ↾ n) := IsFunction.of_mem hbw
    have haT : a ∈ baireTreeBody (baireRunTreePreimage T) := by
      apply (baireRunTreePreimage_body_iff hT.1 ha).mpr
      rw [hea]
      exact hxT
    have hbT : b ∈ baireTreeBody (baireRunTreePreimage T) := by
      apply (baireRunTreePreimage_body_iff hT.1 hb).mpr
      rw [heb]
      exact hyT
    refine ⟨a ↾ n, ((mem_baireTreeBody_iff _ _).mp haT).2 n hn,
      b ↾ n, ((mem_baireTreeBody_iff _ _).mp hbT).2 n hn,
      subset_restrict_of_domain_subset hsa (subset_union_left _ _),
      subset_restrict_of_domain_subset hsb (subset_union_left _ _), i, ?_, ?_, ?_⟩
    · rw [domain_eq_of_mem_function hav]; exact hin
    · rw [domain_eq_of_mem_function hbw]; exact hin
    · rw [value_restrict (by rw [domain_eq_of_mem_function ha]; exact hi) hin,
        value_restrict (by rw [domain_eq_of_mem_function hb]; exact hi) hin]
      exact hne

theorem bairePerfectSetProperty_of_image {A : V} (hA : A ⊆ baireSpace V)
    (hP : PerfectSetProperty (baireRunImage A)) : BairePerfectSetProperty A := by
  rcases hP with hcount | ⟨T, hT, hTA⟩
  · exact Or.inl ((baireRunImage_countable_iff hA).mp hcount)
  · refine Or.inr ⟨baireRunTreePreimage T,
      baireRunTreePreimage_perfect hT (subset_trans hTA (baireRunImage_subset_infiniteOnes hA)), ?_⟩
    intro a haT
    have ha := ((mem_baireTreeBody_iff _ _).mp haT).1
    exact (baireRunCode_mem_image_iff hA ha).mp
      (hTA _ ((baireRunTreePreimage_body_iff hT.1 ha).mp haT))

theorem allBairePerfectSetProperty_of_cantor (h : AllPerfectSetProperty V) :
    ∀ A : V, A ⊆ baireSpace V → BairePerfectSetProperty A :=
  fun _ hA ↦ bairePerfectSetProperty_of_image hA (h _ (baireRunImage_subset_cantor hA))

end ZFVP
