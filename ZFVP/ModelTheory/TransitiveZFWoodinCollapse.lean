import ZFVP.ModelTheory.TransitiveZFRankOperations
import ZFVP.SetTheory.WoodinCollapse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_mem_woodinCollapse_iff (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ δ p : SetDomain (hierarchy ξ)) (hδ : IsOrdinal δ) :
    p ∈ woodinCollapse κ δ ↔ p.val ∈ woodinCollapse κ.val δ.val := by
  let := hierarchy_transitive ξ
  let := hδ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) δ).mp hδ
  rw [mem_woodinCollapse, mem_woodinCollapse, TransitiveZF.subset_val_iff,
    TransitiveZF.prod_val, TransitiveZF.prod_val, rank_hierarchy_val δ hδ,
    TransitiveZF.isFunction_iff, rank_cardinalSmall_iff hs, TransitiveZF.domain_val]
  apply and_congr_right
  intro hsub
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  have hη {a η x : V} (hp : ⟨⟨a, η⟩ₖ, x⟩ₖ ∈ p.val) : η ∈ δ.val :=
    (kpair_mem_iff.mp (kpair_mem_iff.mp (hsub _ hp)).1).2
  have hH (η : SetDomain (hierarchy ξ)) (hηδ : η ∈ δ) :
      (hierarchy (ordinalAdd (1 : SetDomain (hierarchy ξ)) η)).val =
        hierarchy (ordinalAdd (1 : V) η.val) := by
    let := IsOrdinal.of_mem hηδ
    let : IsOrdinal (1 : SetDomain (hierarchy ξ)) := IsOrdinal.of_mem (show
      (1 : SetDomain (hierarchy ξ)) ∈ ω by simp)
    rw [rank_hierarchy_val _ inferInstance, TransitiveZF.ordinalLeftOne_val _ η inferInstance]
  constructor
  · intro h a η x hp
    have hbx := kpair_components_mem_transitive ((hierarchy_transitive ξ).mem_trans hp p.property)
    have haη := kpair_components_mem_transitive hbx.1
    let a' : SetDomain (hierarchy ξ) := ⟨a, haη.1⟩
    let η' : SetDomain (hierarchy ξ) := ⟨η, haη.2⟩
    let x' : SetDomain (hierarchy ξ) := ⟨x, hbx.2⟩
    have hp' : (⟨⟨a', η'⟩ₖ, x'⟩ₖ : SetDomain (hierarchy ξ)) ∈ p := by
      change (⟨⟨a', η'⟩ₖ, x'⟩ₖ : SetDomain (hierarchy ξ)).val ∈ p.val
      simpa only [TransitiveZF.kpair_val] using hp
    have hx := h a' η' x' hp'
    change x ∈ (hierarchy (ordinalAdd (1 : SetDomain (hierarchy ξ)) η')).val at hx
    rwa [hH η' (hη hp)] at hx
  · intro h a η x hp
    have hp' : ⟨⟨a.val, η.val⟩ₖ, x.val⟩ₖ ∈ p.val := by
      change (⟨⟨a, η⟩ₖ, x⟩ₖ : SetDomain (hierarchy ξ)).val ∈ p.val at hp
      simpa only [TransitiveZF.kpair_val] using hp
    change x.val ∈ (hierarchy (ordinalAdd (1 : SetDomain (hierarchy ξ)) η)).val
    rw [hH η (hη hp')]
    exact h a.val η.val x.val hp'

theorem rank_woodinCollapse_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ δ : SetDomain (hierarchy ξ)) (hδ : IsOrdinal δ) :
    (woodinCollapse κ δ).val = woodinCollapse κ.val δ.val := by
  let := hierarchy_transitive ξ
  have hH := rank_hierarchy_val δ hδ
  have hHU : hierarchy δ.val ∈ hierarchy ξ := hH ▸ (hierarchy δ).property
  apply SetTheory.mem_ext_iff.mpr
  intro p
  constructor
  · intro hp
    let p' : SetDomain (hierarchy ξ) :=
      ⟨p, (hierarchy_transitive ξ).mem_trans hp (woodinCollapse κ δ).property⟩
    exact (rank_mem_woodinCollapse_iff hs κ δ p' hδ).mp hp
  · intro hp
    have hpU := subset_mem_hierarchy_limit hs
      (prod_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs κ.property δ.property) hHU)
      ((mem_woodinCollapse _ _ _).mp hp).1
    exact (rank_mem_woodinCollapse_iff hs κ δ ⟨p, hpU⟩ hδ).mpr hp

theorem TransitiveZF.reverseInclusionOrder_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (P : SetDomain U) :
    (reverseInclusionOrder P).val = reverseInclusionOrder P.val := by
  unfold reverseInclusionOrder
  rw [← TransitiveZF.prod_val U P P]
  apply TransitiveZF.sep_val U
  intro s hs
  obtain ⟨p, _, q, _, rfl⟩ := mem_prod_iff.mp hs
  simp only [TransitiveZF.kpair_val U, kpair.π₁_kpair, kpair.π₂_kpair]
  exact TransitiveZF.subset_val_iff U q p

theorem rank_woodinCollapseOrder_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (κ δ : SetDomain (hierarchy ξ)) (hδ : IsOrdinal δ) :
    (woodinCollapseOrder κ δ).val = woodinCollapseOrder κ.val δ.val := by
  let := hierarchy_transitive ξ
  rw [woodinCollapseOrder, TransitiveZF.reverseInclusionOrder_val,
    rank_woodinCollapse_val hs κ δ hδ]
  rfl

end ZFVP
