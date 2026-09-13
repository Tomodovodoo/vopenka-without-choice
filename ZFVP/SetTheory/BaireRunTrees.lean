import ZFVP.SetTheory.BaireRunTopology
import ZFVP.SetTheory.TreeBodies

/-! Pullback of closed and nowhere dense binary trees through the run homeomorphism. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem baireFiniteRunCode_mono {s t : V} (hs : s ∈ naturalSequences V)
    (ht : t ∈ naturalSequences V) (hst : s ⊆ t) : baireFiniteRunCode s ⊆ baireFiniteRunCode t := by
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  obtain ⟨hn, htf⟩ := (mem_finiteSequences_iff_domain _ t).mp ht
  have : IsFunction s := IsFunction.of_mem hsf
  have : IsFunction t := IsFunction.of_mem htf
  have : IsOrdinal (domain t) := IsOrdinal.of_mem hn
  have hdom := sequence_domain_subset_of_subset htf hsf hst
  have he : baireRunPrefix s (domain s) = baireRunPrefix t (domain s) :=
    baireRunPrefix_agree hm (fun i hi ↦ (value_eq_of_subset_function hst hi).symm)
  unfold baireFiniteRunCode
  rw [he]
  exact baireRunPrefix_mono htf hm hn hdom (subset_refl _)

theorem tree_mem_of_binary_subset {T s t : V} (hT : IsTree T) (ht : t ∈ T)
    (hs : s ∈ binarySequences V) (hst : s ⊆ t) : s ∈ T := by
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  obtain ⟨_, htf⟩ := (mem_finiteSequences_iff_domain _ t).mp (hT.1 t ht)
  rw [sequence_eq_restrict_of_subset htf hsf hst]
  exact tree_restrict_mem hT ht hm (sequence_domain_subset_of_subset htf hsf hst)

noncomputable def baireRunTreePreimage (T : V) : V :=
  {s ∈ naturalSequences V ; baireFiniteRunCode s ∈ T}

theorem mem_baireRunTreePreimage_iff (T s : V) :
    s ∈ baireRunTreePreimage T ↔ s ∈ naturalSequences V ∧ baireFiniteRunCode s ∈ T := by
  simp [baireRunTreePreimage]

instance baireRunTreePreimage_definable : ℒₛₑₜ-function₁[V] baireRunTreePreimage := by
  have h : ℒₛₑₜ-relation (fun B T : V ↦
      ∀ s, s ∈ B ↔ s ∈ naturalSequences V ∧ baireFiniteRunCode s ∈ T) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_baireRunTreePreimage_iff]

theorem baireRunTreePreimage_subset (T : V) : baireRunTreePreimage T ⊆ naturalSequences V :=
  fun s hs ↦ ((mem_baireRunTreePreimage_iff T s).mp hs).1

theorem baireRunTreePreimage_isTree {T : V} (hT : IsTree T) : IsBaireTree (baireRunTreePreimage T) := by
  refine ⟨baireRunTreePreimage_subset T, ?_⟩
  intro s hs n hn
  obtain ⟨hsn, hsT⟩ := (mem_baireRunTreePreimage_iff T s).mp hs
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hsn
  have : IsOrdinal (domain s) := IsOrdinal.of_mem hm
  have hnω := IsTransitive.ω.transitive _ hm _ hn
  have hrs : s ↾ n ∈ naturalSequences V := (mem_naturalSequences_iff _).mpr
    ⟨n, hnω, function_restrict_mem hsf (IsOrdinal.toIsTransitive.transitive _ hn)⟩
  exact (mem_baireRunTreePreimage_iff T _).mpr ⟨hrs,
    tree_mem_of_binary_subset hT hsT (baireFiniteRunCode_mem hrs)
      (baireFiniteRunCode_mono hrs hsn (restrict_subset _ _))⟩

theorem baireRunTreePreimage_body_iff {T a : V} (hT : IsTree T) (ha : a ∈ baireSpace V) :
    a ∈ baireTreeBody (baireRunTreePreimage T) ↔ baireRunCode a ∈ treeBody T := by
  constructor
  · intro h
    obtain ⟨_, hall⟩ := (mem_baireTreeBody_iff _ _).mp h
    refine (mem_treeBody_iff T _).mpr ⟨baireRunCode_mem ha, ?_⟩
    intro n hn
    have hp := ((mem_baireRunTreePreimage_iff T _).mp (hall n hn)).2
    rw [baireFiniteRunCode_restrict_real ha hn] at hp
    have hr := restrict_mem_binarySequences (baireRunCode_mem ha) hn
    have hrf := function_restrict_mem (baireRunCode_mem ha) (IsTransitive.transitive _ hn)
    exact tree_mem_of_binary_subset hT hp hr
      (binarySequence_subset_runPrefix ha hr (restrict_subset _ _) hn
        (by rw [domain_eq_of_mem_function hrf]))
  · intro h
    obtain ⟨_, hall⟩ := (mem_treeBody_iff T _).mp h
    refine (mem_baireTreeBody_iff _ _).mpr ⟨ha, ?_⟩
    intro n hn
    have hp := baireRunPrefix_real_mem ha hn
    have he := (subset_iff_restrict_eq (baireRunCode_mem ha) hp).mp (baireRunPrefix_subset_code a hn)
    refine (mem_baireRunTreePreimage_iff T _).mpr ⟨restrict_mem_naturalSequences ha hn, ?_⟩
    rw [baireFiniteRunCode_restrict_real ha hn, ← he]
    exact hall _ (binarySequence_domain_mem hp)

theorem baireRunTreePreimage_nowhereDense {T : V} (hT : IsNowhereDenseTree T) :
    IsNowhereDenseBaireTree (baireRunTreePreimage T) := by
  refine ⟨baireRunTreePreimage_isTree hT.1, ?_⟩
  intro s hs
  obtain ⟨t, ht, hst, htT⟩ := hT.2 _ (baireFiniteRunCode_mem hs)
  let a := cantorRunDecode (cantorOneTail t)
  have hx := cantorOneTail_infiniteOnes ht
  have ha : a ∈ baireSpace V := cantorRunDecode_mem hx
  have hca : baireRunCode a = cantorOneTail t := baireRunCode_decode hx
  have htcode : t ⊆ baireRunCode a := by rw [hca]; exact cantorOneTail_extends ht
  have hsa := baireFiniteRunCode_reflects_subset hs ha (subset_trans hst htcode)
  obtain ⟨hm, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have : IsFunction s := IsFunction.of_mem hsf
  let n := domain s ∪ domain t
  have hn : n ∈ (ω : V) := ordinal_union_mem hm (binarySequence_domain_mem ht)
  let u := a ↾ n
  have hu : u ∈ naturalSequences V := restrict_mem_naturalSequences ha hn
  have hsu : s ⊆ u := subset_restrict_of_domain_subset hsa (subset_union_left _ _)
  have htu : t ⊆ baireFiniteRunCode u := by
    rw [baireFiniteRunCode_restrict_real ha hn]
    exact binarySequence_subset_runPrefix ha ht htcode hn (subset_union_right _ _)
  refine ⟨u, hu, hsu, ?_⟩
  intro huT
  exact htT (tree_mem_of_binary_subset hT.1 ((mem_baireRunTreePreimage_iff T u).mp huT).2 ht htu)

end ZFVP
