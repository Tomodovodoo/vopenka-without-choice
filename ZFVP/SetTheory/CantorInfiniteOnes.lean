import ZFVP.SetTheory.BaireCore
import ZFVP.SetTheory.LebesgueNull
import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.FiniteCofinality

/-! The dense G-delta subset of Cantor space used to represent Baire space.
All witnesses are internal sets, and no choice principle is assumed.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cantorOneAfterFormula : SetTheorySemisentence 2 :=
  f“S n. ∀ s, s ∈ S ↔ s ∈ !binarySequencesFormula ∧
    ∃ k ∈ !domain.dfn s, n ⊆ k ∧ !value.dfn s k = !(numeralFormula 1)”

def cantorInfiniteOnesFormula : SetTheorySemisentence 1 :=
  f“D. ∀ x, x ∈ D ↔ x ∈ !cantorSpaceFormula ∧
    ∀ n ∈ !isω, ∃ k ∈ !isω, n ⊆ k ∧ !value.dfn x k = !(numeralFormula 1)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cantorOneAfter (n : V) : V :=
  {s ∈ binarySequences V ; ∃ k ∈ domain s, n ⊆ k ∧ s ‘ k = 1}

theorem mem_cantorOneAfter_iff (n s : V) :
    s ∈ cantorOneAfter n ↔ s ∈ binarySequences V ∧ ∃ k ∈ domain s, n ⊆ k ∧ s ‘ k = 1 := by
  simp [cantorOneAfter]

instance cantorOneAfterFormula_defined :
    ℒₛₑₜ-function₁[V] cantorOneAfter via cantorOneAfterFormula :=
  ⟨fun v ↦ by simp [cantorOneAfterFormula, mem_ext_iff (y := cantorOneAfter _),
    mem_cantorOneAfter_iff]⟩

instance cantorOneAfter_definable : ℒₛₑₜ-function₁[V] cantorOneAfter :=
  cantorOneAfterFormula_defined.to_definable

theorem cantorOneAfter_subset (n : V) : cantorOneAfter n ⊆ binarySequences V :=
  fun s hs ↦ ((mem_cantorOneAfter_iff n s).mp hs).1

theorem cantorOneAfter_dense {n : V} (hn : n ∈ (ω : V)) :
    ∀ s ∈ binarySequences V, ∃ t ∈ cantorOneAfter n, s ⊆ t := by
  intro s hs
  obtain ⟨m, hm, hsm⟩ := (mem_binarySequences_iff s).mp hs
  let k := n ∪ m
  have hk : k ∈ (ω : V) := ordinal_union_mem hn hm
  obtain ⟨u, hu, hsu⟩ := sequence_extend (show (∅ : V) ∈ ((2 : ℕ) : V) by simp [zero_def])
    hsm (subset_union_right n m)
  let t := insert (⟨k, (1 : V)⟩ₖ : V) u
  have ht : t ∈ ((2 : ℕ) : V) ^ succ k :=
    function_append_mem hu (by simp)
  have : IsFunction t := IsFunction.of_mem ht
  refine ⟨t, (mem_cantorOneAfter_iff n t).mpr ⟨
    (mem_binarySequences_iff t).mpr ⟨succ k, ω_succ_closed hk, ht⟩, k, ?_,
    subset_union_left n m, ?_⟩, ?_⟩
  · rw [domain_eq_of_mem_function ht]
    exact mem_succ_self k
  · exact value_eq_of_kpair_mem (show (⟨k, (1 : V)⟩ₖ : V) ∈ t by simp [t])
  · intro p hp
    exact mem_insert.mpr (Or.inr (hsu p hp))

theorem mem_openFrom_cantorOneAfter_iff {n x : V} (hx : x ∈ cantorSpace V) :
    x ∈ openFrom (cantorOneAfter n) ↔ ∃ k ∈ (ω : V), n ⊆ k ∧ x ‘ k = 1 := by
  have : IsFunction x := IsFunction.of_mem hx
  constructor
  · intro h
    obtain ⟨_, s, hs, hxs⟩ := (mem_openFrom_iff _ _).mp h
    obtain ⟨hsb, k, hk, hnk, hsk⟩ := (mem_cantorOneAfter_iff n s).mp hs
    have : IsFunction s := binarySequence_isFunction hsb
    have hsub : s ⊆ x := (subset_iff_restrict_eq hx hsb).mpr hxs
    refine ⟨k, IsTransitive.ω.transitive _ (binarySequence_domain_mem hsb) _ hk, hnk, ?_⟩
    exact (value_eq_of_kpair_mem (hsub _ (kpair_value_mem hk))).trans hsk
  · rintro ⟨k, hk, hnk, hxk⟩
    let s := x ↾ (succ k)
    have hs : s ∈ binarySequences V := restrict_mem_binarySequences hx (ω_succ_closed hk)
    have hsf : s ∈ ((2 : ℕ) : V) ^ succ k :=
      function_restrict_mem hx (IsTransitive.transitive _ (ω_succ_closed hk))
    have : IsFunction s := IsFunction.of_mem hsf
    have hks : k ∈ domain s := by rw [domain_eq_of_mem_function hsf]; exact mem_succ_self k
    have hval : s ‘ k = x ‘ k :=
      value_restrict (by rw [domain_eq_of_mem_function hx]; exact hk) (mem_succ_self k)
    refine (mem_openFrom_iff _ _).mpr ⟨hx, s,
      (mem_cantorOneAfter_iff n s).mpr ⟨hs, k, hks, hnk, hval.trans hxk⟩, ?_⟩
    exact (subset_iff_restrict_eq hx hs).mp (restrict_subset x (succ k))

noncomputable def cantorInfiniteOnes (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {x ∈ cantorSpace V ; ∀ n ∈ (ω : V), ∃ k ∈ (ω : V), n ⊆ k ∧ x ‘ k = 1}

theorem mem_cantorInfiniteOnes_iff (x : V) :
    x ∈ cantorInfiniteOnes V ↔ x ∈ cantorSpace V ∧
      ∀ n ∈ (ω : V), ∃ k ∈ (ω : V), n ⊆ k ∧ x ‘ k = 1 := by
  simp [cantorInfiniteOnes]

instance cantorInfiniteOnesFormula_defined :
    ℒₛₑₜ-function₀[V] (cantorInfiniteOnes V) via cantorInfiniteOnesFormula :=
  ⟨fun v ↦ by simp [cantorInfiniteOnesFormula,
    mem_ext_iff (y := cantorInfiniteOnes V), mem_cantorInfiniteOnes_iff]⟩

noncomputable def cantorOneAfterFamily (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  definableGraph (ω : V) cantorOneAfter cantorOneAfter_definable

theorem cantorOneAfterFamily_mem :
    cantorOneAfterFamily V ∈ (℘ (binarySequences V)) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n _ ↦ mem_power_iff.mpr (cantorOneAfter_subset n))

theorem cantorInfiniteOnes_eq_gDelta : cantorInfiniteOnes V = gDelta (cantorOneAfterFamily V) := by
  apply mem_ext
  intro x
  rw [mem_cantorInfiniteOnes_iff, mem_gDelta_iff]
  constructor <;> rintro ⟨hx, h⟩ <;> refine ⟨hx, ?_⟩ <;> intro n hn
  · rw [cantorOneAfterFamily, value_definableGraph _ _ _ hn]
    exact (mem_openFrom_cantorOneAfter_iff hx).mpr (h n hn)
  · have h' := h n hn
    rw [cantorOneAfterFamily, value_definableGraph _ _ _ hn] at h'
    exact (mem_openFrom_cantorOneAfter_iff hx).mp h'

theorem cantorInfiniteOnes_complement_meagre :
    IsMeagre ((cantorSpace V) \ cantorInfiniteOnes V) := by
  have hF : ℒₛₑₜ-function₁ (fun n : V ↦ avoidingTree (cantorOneAfter n)) := by definability
  let f := definableGraph (ω : V) (fun n ↦ avoidingTree (cantorOneAfter n)) hF
  refine ⟨f, definableGraph_mem_function_of_mapsTo _ _ _ hF
    (fun n _ ↦ mem_power_iff.mpr (avoidingTree_isTree _).1), ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact avoidingTree_nowhereDense (cantorOneAfter_subset n) (cantorOneAfter_dense hn)
  · intro x hx
    obtain ⟨hxc, hxD⟩ := mem_sdiff_iff.mp hx
    have hfails : ¬∀ n ∈ (ω : V), ∃ k ∈ (ω : V), n ⊆ k ∧ x ‘ k = 1 :=
      fun h ↦ hxD ((mem_cantorInfiniteOnes_iff x).mpr ⟨hxc, h⟩)
    push Not at hfails
    obtain ⟨n, hn, hnfail⟩ := hfails
    refine ⟨n, hn, ?_⟩
    rw [value_definableGraph _ _ _ hn]
    apply (mem_treeBody_avoidingTree_iff (cantorOneAfter_subset n) hxc).mpr
    intro hmeet
    obtain ⟨k, hk, hnk, hxk⟩ := (mem_openFrom_cantorOneAfter_iff hxc).mp
      ((mem_openFrom_iff_meets _ _).mpr ⟨hxc, hmeet⟩)
    exact hnfail k hk hnk hxk

noncomputable def cantorOneTailBit (s i : V) : V :=
  {z ∈ (1 : V) ; i ∉ domain s ∨ s ‘ i = 1}

instance cantorOneTailBit_definable : ℒₛₑₜ-function₂[V] cantorOneTailBit := by
  have h : ℒₛₑₜ-relation₃ (fun y s i : V ↦
      ∀ z, z ∈ y ↔ z ∈ (1 : V) ∧ (i ∉ domain s ∨ s ‘ i = 1)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cantorOneTailBit (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [cantorOneTailBit]

theorem cantorOneTailBit_eq_one {s i : V} (h : i ∉ domain s ∨ s ‘ i = 1) :
    cantorOneTailBit s i = 1 := by
  apply mem_ext
  intro z
  simp [cantorOneTailBit, h]

theorem cantorOneTailBit_eq_zero {s i : V} (h : ¬(i ∉ domain s ∨ s ‘ i = 1)) :
    cantorOneTailBit s i = 0 := by
  apply mem_ext
  intro z
  simp [cantorOneTailBit, h, zero_def]

theorem cantorOneTailBit_mem_two (s i : V) : cantorOneTailBit s i ∈ ((2 : ℕ) : V) := by
  by_cases h : i ∉ domain s ∨ s ‘ i = 1
  · rw [cantorOneTailBit_eq_one h]; simp
  · rw [cantorOneTailBit_eq_zero h]; simp

noncomputable def cantorOneTail (s : V) : V :=
  definableGraph (ω : V) (cantorOneTailBit s) (by definability)

theorem cantorOneTail_mem (s : V) : cantorOneTail s ∈ cantorSpace V :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i _ ↦ cantorOneTailBit_mem_two s i)

theorem cantorOneTail_value {s i : V} (hi : i ∈ (ω : V)) :
    (cantorOneTail s) ‘ i = cantorOneTailBit s i := value_definableGraph _ _ _ hi

theorem cantorOneTail_extends {s : V} (hs : s ∈ binarySequences V) : s ⊆ cantorOneTail s := by
  have : IsFunction s := binarySequence_isFunction hs
  intro p hp
  obtain ⟨m, hm, hsm⟩ := (mem_binarySequences_iff s).mp hs
  obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hsm p hp)
  have hiω : i ∈ (ω : V) := IsTransitive.ω.transitive m hm i hi
  have hid : i ∈ domain s := mem_domain_of_kpair_mem hp
  have hsy := value_eq_of_kpair_mem hp
  apply (pair_mem_definableGraph_iff _ _ _ _ _).mpr
  refine ⟨hiω, ?_⟩
  rcases show y = (0 : V) ∨ y = 1 from by simpa using hy with rfl | rfl
  · exact (cantorOneTailBit_eq_zero (by simp [hid, hsy, LO.FirstOrder.SetTheory.zero_ne_one])).symm
  · exact (cantorOneTailBit_eq_one (Or.inr hsy)).symm

theorem cantorOneTail_infiniteOnes {s : V} (hs : s ∈ binarySequences V) :
    cantorOneTail s ∈ cantorInfiniteOnes V := by
  refine (mem_cantorInfiniteOnes_iff _).mpr ⟨cantorOneTail_mem s, ?_⟩
  intro n hn
  let k := n ∪ domain s
  have hk : k ∈ (ω : V) := ordinal_union_mem hn (binarySequence_domain_mem hs)
  refine ⟨k, hk, subset_union_left _ _, ?_⟩
  rw [cantorOneTail_value hk]
  exact cantorOneTailBit_eq_one (Or.inl (fun h ↦ mem_irrefl k (subset_union_right n (domain s) k h)))

/-- Every basic Cantor open set meets the specified G-delta. -/
theorem cantorInfiniteOnes_dense :
    ∀ s ∈ binarySequences V, ∃ x ∈ cantorInfiniteOnes V, x ↾ (domain s) = s := by
  intro s hs
  exact ⟨cantorOneTail s, cantorOneTail_infiniteOnes hs,
    (subset_iff_restrict_eq (cantorOneTail_mem s) hs).mp (cantorOneTail_extends hs)⟩

end ZFVP
