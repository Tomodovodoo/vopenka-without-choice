import ZFVP.SetTheory.BinaryShadowWeightsSums
import ZFVP.SetTheory.PerfectSetCore

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryDisjointUnion_cardEQ {A B : V} (hd : ∀ x, x ∈ A → x ∈ B → False) :
    (A ∪ B) ≋ disjointUnion A B := by
  refine ⟨union_cardLE_disjointUnion _ _, ?_⟩
  refine cardLE_of_injective_map kpair.π₁ (by definability) ?_ ?_
  · intro z hz
    rcases (mem_disjointUnion_iff _ _ _).mp hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact mem_union_iff.mpr (Or.inl (by simpa using ha))
    · exact mem_union_iff.mpr (Or.inr (by simpa using hb))
  · intro z hz w hw he
    rcases (mem_disjointUnion_iff _ _ _).mp hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases (mem_disjointUnion_iff _ _ _).mp hw with ⟨c, hc, rfl⟩ | ⟨d, hd', rfl⟩ <;>
      simp only [kpair.π₁_kpair] at he
    · rw [he]
    · exact (hd a ha (he.symm ▸ hd')).elim
    · exact (hd b (he.symm ▸ hc) hb).elim
    · rw [he]

theorem binaryFiniteCard_disjoint_union {A B : V} (hA : IsInternallyFinite A)
    (hB : IsInternallyFinite B) (hd : ∀ x, x ∈ A → x ∈ B → False) :
    binaryFiniteCard (A ∪ B) = ordinalAdd (binaryFiniteCard A) (binaryFiniteCard B) := by
  obtain ⟨ha, hea⟩ := binaryFiniteCard_spec hA
  obtain ⟨hb, heb⟩ := binaryFiniteCard_spec hB
  apply binaryFiniteCard_eq (ordinalAdd_natural ha hb)
  exact (ordinalAdd_natural_cardEQ ha hb).trans
    ((show disjointUnion (binaryFiniteCard A) (binaryFiniteCard B) ≋ disjointUnion A B from
      ⟨disjointUnion_cardLE hea.le heb.le, disjointUnion_cardLE hea.ge heb.ge⟩).trans
      (binaryDisjointUnion_cardEQ hd).symm)

theorem binaryFiniteCard_singleton (s : V) : binaryFiniteCard ({s} : V) = 1 := by
  apply binaryFiniteCard_eq (by simp)
  constructor
  · refine cardLE_of_injective_map (fun _ ↦ s) (by definability) (by simp) ?_
    intro x hx y hy he
    have hx0 : x = (0 : V) := by simpa only [show (1 : V) = succ ∅ from rfl, mem_succ_iff, not_mem_empty, or_false, zero_def] using hx
    have hy0 : y = (0 : V) := by simpa only [show (1 : V) = succ ∅ from rfl, mem_succ_iff, not_mem_empty, or_false, zero_def] using hy
    exact hx0.trans hy0.symm
  · refine cardLE_of_injective_map (fun _ ↦ (0 : V)) (by definability) ?_ ?_
    · intro x hx
      exact mem_succ_self _
    · intro x hx y hy he
      exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm

theorem binaryShadow_singleton_self {s : V} (hs : s ∈ binarySequences V) :
    shadow ({s} : V) (domain s) = ({s} : V) := by
  obtain ⟨n, hn, hsn⟩ := (mem_binarySequences_iff s).mp hs
  have : IsFunction s := IsFunction.of_mem hsn
  apply mem_ext
  intro t
  rw [mem_shadow_iff, mem_singleton_iff]
  constructor
  · rintro ⟨ht, u, hu, hut⟩
    have hus := mem_singleton_iff.mp hu
    subst u
    have : IsFunction t := IsFunction.of_mem ht
    have he := restrict_domain_eq_of_subset hut
    have htself := IsFunction.restrict_eq_self t (domain s)
      (by rw [domain_eq_of_mem_function ht])
    exact htself.symm.trans he
  · rintro rfl
    exact ⟨by rwa [domain_eq_of_mem_function hsn], t, by simp, subset_refl _⟩

theorem binaryShadowWeight_singleton {s M : V} (hs : s ∈ binarySequences V)
    (hM : M ∈ (ω : V)) (hd : domain s ⊆ M) :
    binaryShadowWeight ({s} : V) M = dyadicUnit (domain s) := by
  rw [binaryShadowWeight_stable (binarySequence_domain_mem hs) hM
    (by intro t ht; simpa only [mem_singleton_iff.mp ht] using subset_refl (domain s)) hd]
  unfold binaryShadowWeight
  rw [binaryShadow_singleton_self hs, binaryFiniteCard_singleton]
  exact congrArg Subtype.val (one_mul (⟨dyadicUnit (domain s), dyadicUnit_mem (binarySequence_domain_mem hs)⟩ : InternalRational V))

theorem binaryShadowWeight_disjoint_union {E D M : V} (hM : M ∈ (ω : V))
    (hd : ∀ t, t ∈ shadow E M → t ∈ shadow D M → False) :
    binaryShadowWeight (E ∪ D) M = rationalAdd (binaryShadowWeight E M) (binaryShadowWeight D M) := by
  unfold binaryShadowWeight
  rw [shadow_union, binaryFiniteCard_disjoint_union (shadow_finite hM) (shadow_finite hM) hd]
  let a : InternalNatural V := ⟨binaryFiniteCard (shadow E M), (binaryFiniteCard_spec (shadow_finite hM)).1⟩
  let b : InternalNatural V := ⟨binaryFiniteCard (shadow D M), (binaryFiniteCard_spec (shadow_finite hM)).1⟩
  let d : InternalRational V := ⟨dyadicUnit M, dyadicUnit_mem hM⟩
  have he : InternalRational.ofNatural (a + b) * d = InternalRational.ofNatural a * d + InternalRational.ofNatural b * d := by
    rw [InternalRational.ofNatural_add, add_mul]
  exact congrArg Subtype.val he

end ZFVP
