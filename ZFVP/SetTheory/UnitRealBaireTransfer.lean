import ZFVP.SetTheory.RealCategoryClosure

/-! Cantor BP transfers to actual unit-interval reals through the closed binary map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem unitReal_interior_of_ne_endpoints {x : V} (hx : x ∈ unitReals V)
    (h0 : x ≠ rationalCut (rationalZero V)) (h1 : x ≠ rationalCut (rationalOne V)) :
    x ∈ realInterval (rationalZero V) (rationalOne V) := by
  obtain ⟨hxCut, h0x, hx1⟩ := (mem_unitReals_iff _).mp hx
  exact (mem_realInterval_iff _ _ _).mpr ⟨hxCut, ⟨h0x, Ne.symm h0⟩, ⟨hx1, h1⟩⟩

theorem realUnitInterior_subset_unit :
    realInterval (rationalZero V) (rationalOne V) ⊆ unitReals V := by
  intro x hx
  obtain ⟨hxCut, h0x, hx1⟩ := (mem_realInterval_iff _ _ _).mp hx
  exact (mem_unitReals_iff _).mpr ⟨hxCut, h0x.1, hx1.1⟩

theorem unitRealBaireProperty_of_preimage {A : V} (hA : A ⊆ unitReals V)
    (hBP : BaireProperty (binaryPreimage A)) : RealBaireProperty A := by
  obtain ⟨_, ⟨S, hS, rfl⟩, hM⟩ := hBP
  let M := ((binaryPreimage A) \ openFrom S) ∪ ((openFrom S) \ binaryPreimage A)
  let K := binaryImage (treeBody (avoidingTree S))
  let W := realInterval (rationalZero V) (rationalOne V) ∩ ((dedekindReals V) \ K)
  let E := ({rationalCut (rationalZero V)} : V) ∪ {rationalCut (rationalOne V)}
  have hE : IsRealNowhereDense E := realNowhereDense_union
    (realSingleton_nowhereDense (rationalCut_isCut rationalZero_mem))
    (realSingleton_nowhereDense (rationalCut_isCut rationalOne_mem))
  have hEo : IsRealOpen ((dedekindReals V) \ E) := realComplement_union_open
    (realSingleton_complement_open (rationalCut_isCut rationalZero_mem))
    (realSingleton_complement_open (rationalCut_isCut rationalOne_mem))
  have hWo : IsRealOpen W := isRealOpen_inter (realInterval_isOpen rationalZero_mem rationalOne_mem)
    (binaryTreeImage_complement_open (avoidingTree_isTree S))
  refine ⟨W, hWo, isRealMeagre_subset
    (isRealMeagre_union_closed_nowhereDense (binaryImage_meagre hM) hE hEo) ?_⟩
  intro x hx
  change x ∈ (binaryImage M) ∪ E
  rcases mem_union_iff.mp hx with hxAW | hxWA
  · obtain ⟨hxA, hxW⟩ := mem_sdiff_iff.mp hxAW
    by_cases hxE : x ∈ E
    · exact mem_union_iff.mpr (Or.inr hxE)
    have h0 : x ≠ rationalCut (rationalZero V) := by
      intro he
      apply hxE
      simp [E, he]
    have h1 : x ≠ rationalCut (rationalOne V) := by
      intro he
      apply hxE
      simp [E, he]
    have hxi := unitReal_interior_of_ne_endpoints (hA x hxA) h0 h1
    have hxR := realInterval_subset_reals _ _ x hxi
    have hxK : x ∈ K := by
      by_contra hxK
      exact hxW (mem_inter_iff.mpr ⟨hxi, mem_sdiff_iff.mpr ⟨hxR, hxK⟩⟩)
    obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hxK
    have hcC := treeBody_subset_cantorSpace (avoidingTree S) c hc
    have hcnot : c ∉ openFrom S := by
      intro hcu
      exact ((mem_treeBody_avoidingTree_iff hS hcC).mp hc) ((mem_openFrom_iff_meets _ _).mp hcu).2
    apply mem_union_iff.mpr ∘ Or.inl
    exact (mem_binaryImage_iff _ _).mpr ⟨c, mem_union_iff.mpr (Or.inl
      (mem_sdiff_iff.mpr ⟨(mem_binaryPreimage_iff _ _).mpr ⟨hcC, hxA⟩, hcnot⟩)), rfl⟩
  · obtain ⟨hxW, hxA⟩ := mem_sdiff_iff.mp hxWA
    obtain ⟨hxi, hxRK⟩ := mem_inter_iff.mp hxW
    have hxK := (mem_sdiff_iff.mp hxRK).2
    obtain ⟨c, hcC, rfl⟩ := binaryReal_surjective (realUnitInterior_subset_unit x hxi)
    have hcU : c ∈ openFrom S := by
      by_contra hcU
      have hcT : c ∈ treeBody (avoidingTree S) :=
        (mem_treeBody_avoidingTree_iff hS hcC).mpr (fun hmeet ↦ hcU
          ((mem_openFrom_iff_meets _ _).mpr ⟨hcC, hmeet⟩))
      exact hxK ((mem_binaryImage_iff _ _).mpr ⟨c, hcT, rfl⟩)
    have hcnot : c ∉ binaryPreimage A := fun hc ↦ hxA ((mem_binaryPreimage_iff _ _).mp hc).2
    exact mem_union_iff.mpr (Or.inl ((mem_binaryImage_iff _ _).mpr ⟨c,
      mem_union_iff.mpr (Or.inr (mem_sdiff_iff.mpr ⟨hcU, hcnot⟩)), rfl⟩))

theorem allUnitRealBaireProperty_of_cantor (h : AllBaireProperty V) :
    ∀ A : V, A ⊆ unitReals V → RealBaireProperty A := by
  intro A hA
  apply unitRealBaireProperty_of_preimage hA
  exact h _ (fun c hc ↦ ((mem_binaryPreimage_iff _ _).mp hc).1)

end ZFVP
