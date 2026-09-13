import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Small collapses have a canonical graph, obtained by internal recursion. -/
theorem HasSmallTransitiveCollapse.canonical {κ X : V}
    (h : HasSmallTransitiveCollapse κ X) :
    range (mostowskiMap (membershipRelation X) X) ∈ hierarchy κ ∧
      IsTransitiveCollapse (membershipRelation X) X
        (range (mostowskiMap (membershipRelation X) X))
        (mostowskiMap (membershipRelation X) X) := by
  obtain ⟨C, hC, f, hf⟩ := h
  have hu := transitiveCollapse_unique (membershipRelation_wellFounded X) hf
  rw [mostowskiMap_of_wellFounded (membershipRelation_wellFounded X)]
  rw [hu.1, hu.2] at hf
  exact ⟨hu.2 ▸ hC, hf⟩

/-- A collapse is injective as an internal graph. -/
theorem IsTransitiveCollapse.injective {R X C f : V}
    (hf : IsTransitiveCollapse R X C f) : Injective f := by
  have : IsFunction f := IsFunction.of_mem hf.2.1
  intro x y z hx hy
  exact hf.2.2.2.1 x (domain_eq_of_mem_function hf.2.1 ▸ mem_domain_of_kpair_mem hx)
    y (domain_eq_of_mem_function hf.2.1 ▸ mem_domain_of_kpair_mem hy)
    ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)

/-- A union indexed inside a small collapse is a surjective image of `Vκ`
when each member has a small collapse and contains a common element. -/
theorem smallCollapse_union_surjection {κ Y F x : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hY : HasSmallTransitiveCollapse κ Y)
    (hne : IsNonempty (F ∩ Y))
    (hF : ∀ Z ∈ F ∩ Y, HasSmallTransitiveCollapse κ Z)
    (hx : ∀ Z ∈ F ∩ Y, x ∈ Z) :
    ∃ e ∈ (⋃ˢ (F ∩ Y)) ^ (hierarchy κ), range e = ⋃ˢ (F ∩ Y) := by
  classical
  let c : V → V := fun Z ↦ mostowskiMap (membershipRelation Z) Z
  have hc : ℒₛₑₜ-function₁ c := by unfold c; definability
  let d : V → V := fun Z ↦ converseGraph (c Z)
  have hd : ℒₛₑₜ-function₁ d := by unfold d; definability
  let v : V → V := fun p ↦ (d ((d Y) ‘ (kpair.π₁ p))) ‘ (kpair.π₂ p)
  have hv : ℒₛₑₜ-function₁ v := by unfold v; definability
  let E : V → V := fun p ↦ if v p ∈ ⋃ˢ (F ∩ Y) then v p else x
  have hE : ℒₛₑₜ-function₁ E := by
    have ht : ℒₛₑₜ-relation (fun y p : V ↦
        (v p ∈ ⋃ˢ (F ∩ Y) ∧ y = v p) ∨ (v p ∉ ⋃ˢ (F ∩ Y) ∧ y = x)) := by definability
    apply Language.Definable.of_iff ht
    intro q
    change q 0 = E (q 1) ↔ _
    by_cases hq : v (q 1) ∈ ⋃ˢ (F ∩ Y) <;> simp [E, hq]
  have hxU : x ∈ ⋃ˢ (F ∩ Y) := by
    obtain ⟨Z, hZ⟩ := hne
    exact mem_sUnion_iff.mpr ⟨Z, hZ, hx Z hZ⟩
  have hmaps : ∀ p ∈ hierarchy κ, E p ∈ ⋃ˢ (F ∩ Y) := by
    intro p _
    dsimp only [E]
    split_ifs with hp
    · exact hp
    · exact hxU
  refine ⟨definableGraph (hierarchy κ) E hE,
    definableGraph_mem_function_of_mapsTo _ _ E hE hmaps, ?_⟩
  apply mem_ext
  intro z
  rw [mem_range_iff]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hpκ, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hp
    exact hmaps p hpκ
  · intro hz
    obtain ⟨Z, hZ, hzZ⟩ := mem_sUnion_iff.mp hz
    have hZY := (mem_inter_iff.mp hZ).2
    obtain ⟨hcYκ, hcY⟩ := hY.canonical
    obtain ⟨hcZκ, hcZ⟩ := (hF Z hZ).canonical
    have haκ : (c Y) ‘ Z ∈ hierarchy κ := (hierarchy_transitive κ).mem_trans
      (function_value_mem hcY.2.1 hZY) hcYκ
    have hbκ : (c Z) ‘ z ∈ hierarchy κ := (hierarchy_transitive κ).mem_trans
      (function_value_mem hcZ.2.1 hzZ) hcZκ
    have hdY : (d Y) ‘ ((c Y) ‘ Z) = Z :=
      converseGraph_value_value hcY.2.1 hcY.injective hZY
    have hdZ : (d Z) ‘ ((c Z) ‘ z) = z :=
      converseGraph_value_value hcZ.2.1 hcZ.injective hzZ
    have hpairκ := kpair_mem_hierarchy_limit hκ haκ hbκ
    have hvz : v ⟨(c Y) ‘ Z, (c Z) ‘ z⟩ₖ = z := by
      dsimp only [v]
      rw [kpair.π₁_kpair, kpair.π₂_kpair, hdY, hdZ]
    refine ⟨⟨(c Y) ‘ Z, (c Z) ‘ z⟩ₖ,
      (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hpairκ, ?_⟩⟩
    simp only [E, hvz, hz, ↓reduceIte]

end ZFVP


