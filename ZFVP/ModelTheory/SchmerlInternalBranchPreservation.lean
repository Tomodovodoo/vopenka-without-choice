import ZFVP.ModelTheory.SchmerlInternalBMR
import ZFVP.SetTheory.ProductForcing
import ZFVP.SetTheory.HartogsRegular

/-! The splitting-antichain argument inside the ground ZF model. In particular,
the splitting set, its antichain, the witness family, and its rank bound are
internal sets. The forcing-name interpretation is treated separately. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Local properties of an internal condition/node relation. -/
structure InternalBranchRelation (P R T S κ rank E base : V) : Prop where
  rank_function : rank ∈ κ ^ T
  rank_monotone : ∀ x ∈ T, ∀ y ∈ T, ⟨x, y⟩ₖ ∈ S → (rank ‘ x) ⊆ (rank ‘ y)
  below_linear : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
    ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S
  monotone : ∀ p ∈ P, ∀ q ∈ P, ∀ x ∈ T,
    ⟨p, q⟩ₖ ∈ R → ⟨q, x⟩ₖ ∈ E → ⟨p, x⟩ₖ ∈ E
  chain : ∀ p ∈ P, ∀ x ∈ T, ∀ y ∈ T,
    ⟨p, x⟩ₖ ∈ E → ⟨p, y⟩ₖ ∈ E → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S
  cofinal : ∀ p ∈ P, ⟨p, base⟩ₖ ∈ R → ∀ i ∈ κ,
    ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ∃ x ∈ T, ⟨q, x⟩ₖ ∈ E ∧ i ⊆ (rank ‘ x)

noncomputable def internalPossibleNodes (P R T E p : V) : V :=
  {x ∈ T ; ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q, x⟩ₖ ∈ E}

instance internalPossibleNodes_definable (P R T E : V) :
    ℒₛₑₜ-function₁[V] (internalPossibleNodes P R T E) := by
  have h : ℒₛₑₜ-relation[V] (fun B p ↦ ∀ x,
      x ∈ B ↔ x ∈ T ∧ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q, x⟩ₖ ∈ E) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalPossibleNodes P R T E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [internalPossibleNodes, mem_sep_iff]

def InternalStabilizes (P R T S E p : V) : Prop :=
  ∀ x ∈ internalPossibleNodes P R T E p, ∀ y ∈ internalPossibleNodes P R T E p,
    ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S

instance internalStabilizes_definable (P R T S E : V) :
    ℒₛₑₜ-predicate[V] (InternalStabilizes P R T S E) := by
  unfold InternalStabilizes
  definability

noncomputable def internalSplittingPairs (P T S E : V) : V :=
  {a ∈ P ×ˢ P ; ∃ x ∈ T, ∃ y ∈ T,
    ⟨kpair.π₁ a, x⟩ₖ ∈ E ∧ ⟨kpair.π₂ a, y⟩ₖ ∈ E ∧
      ¬ (⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)}

theorem InternalBranchRelation.comparable_of_compatible
    {P R T S κ rank E base p q x y : V}
    (h : InternalBranchRelation P R T S κ rank E base)
    (hp : p ∈ P) (hq : q ∈ P) (hx : x ∈ T) (hy : y ∈ T)
    (hc : ForcingCompatible P R p q) (hpx : ⟨p, x⟩ₖ ∈ E) (hqy : ⟨q, y⟩ₖ ∈ E) :
    ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S := by
  obtain ⟨r, hr, hrp, hrq⟩ := hc
  exact h.chain r hr x hx y hy
    (h.monotone r hr p hp x hx hrp hpx) (h.monotone r hr q hq y hy hrq hqy)

set_option maxHeartbeats 1600000 in
/-- Internal ccc of the square makes the stabilizing conditions dense below
the condition forcing cofinality. -/
theorem internal_stabilizes_dense_below (hAC : InternalChoice V)
    {P R T S κ rank E base : V} (hR : IsForcingPreorder P R)
    (h : InternalBranchRelation P R T S κ rank E base)
    (hreg : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hccc : ∀ A : V, IsForcingAntichain (P ×ˢ P) (productOrder P R P R) A →
      IsInternallyCountable A) :
    ForcingDenseBelow P R {p ∈ P ; InternalStabilizes P R T S E p} base := by
  classical
  have : IsOrdinal κ := hreg.1.1
  let Q := productOrder P R P R
  have hQ : IsForcingPreorder (P ×ˢ P) Q := productOrder_preorder hR hR
  let Split := internalSplittingPairs P T S E
  have hSplit : Split ⊆ P ×ˢ P := sep_subset
  obtain ⟨A, hanti, hASplit, hmax⟩ := exists_maximalAntichain hQ hSplit
    (wellOrderable_of_internalChoice hAC Split)
  have hACount := hccc A hanti
  let Witnesses : V → V := fun a ↦ {z ∈ T ×ˢ T ;
    ⟨kpair.π₁ a, kpair.π₁ z⟩ₖ ∈ E ∧ ⟨kpair.π₂ a, kpair.π₂ z⟩ₖ ∈ E ∧
      ¬ (⟨kpair.π₁ z, kpair.π₂ z⟩ₖ ∈ S ∨ ⟨kpair.π₂ z, kpair.π₁ z⟩ₖ ∈ S)}
  have hW : ℒₛₑₜ-function₁ Witnesses := internal_fiber_definable (T ×ˢ T) _ (by definability)
  have hWne : ∀ a ∈ A, IsNonempty (Witnesses a) := by
    intro a ha
    obtain ⟨_, x, hx, y, hy, hpx, hqy, hxy⟩ := mem_sep_iff.mp (hASplit a ha)
    refine ⟨⟨⟨x, y⟩ₖ, mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hx, hy⟩, ?_⟩⟩⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hpx (And.intro hqy hxy)
  obtain ⟨g, _, _, hg⟩ := choice_for_definable_family hAC A Witnesses hW hWne
  let left : V → V := fun a ↦ kpair.π₁ (g ‘ a)
  let right : V → V := fun a ↦ kpair.π₂ (g ‘ a)
  have hnodes (a : V) (ha : a ∈ A) : left a ∈ T ∧ right a ∈ T := by
    have hprod := (mem_sep_iff.mp (hg a ha)).1
    obtain ⟨x, hx, y, hy, he⟩ := mem_prod_iff.mp hprod
    change kpair.π₁ (g ‘ a) ∈ T ∧ kpair.π₂ (g ‘ a) ∈ T
    rw [he]
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hx hy
  have hforces (a : V) (ha : a ∈ A) :
      ⟨kpair.π₁ a, left a⟩ₖ ∈ E ∧ ⟨kpair.π₂ a, right a⟩ₖ ∈ E ∧
        ¬ (⟨left a, right a⟩ₖ ∈ S ∨ ⟨right a, left a⟩ₖ ∈ S) :=
    (mem_sep_iff.mp (hg a ha)).2
  have hL : ℒₛₑₜ-function₁ (fun a ↦ rank ‘ (left a)) := by dsimp [left]; definability
  have hU : ℒₛₑₜ-function₁ (fun a ↦ rank ‘ (right a)) := by dsimp [right]; definability
  let B : V := repl (fun a ↦ rank ‘ (left a)) hL A ∪ repl (fun a ↦ rank ‘ (right a)) hU A
  have hBC : IsInternallyCountable B := internallyCountable_union
    (internallyCountable_repl _ hL hACount) (internallyCountable_repl _ hU hACount)
  have hBκ : B ⊆ κ := by
    intro ξ hξ
    rcases mem_union_iff.mp hξ with hξ | hξ
    · obtain ⟨a, ha, rfl⟩ := (repl_spec hL).mp hξ
      exact function_value_mem h.rank_function (hnodes a ha).1
    · obtain ⟨a, ha, rfl⟩ := (repl_spec hU).mp hξ
      exact function_value_mem h.rank_function (hnodes a ha).2
  obtain ⟨i, hi, hBi⟩ := regular_small_subset_bounded hreg hBκ hω hBC
  refine ⟨sep_subset, fun p hp hpb ↦ ?_⟩
  obtain ⟨q, hq, hqp, z, hz, hqz, hiz⟩ := h.cofinal p hp hpb i hi
  have hnone : ∀ a ∈ A, ¬ ForcingCompatible (P ×ˢ P) Q ⟨q, q⟩ₖ a := by
    intro a ha hc
    obtain ⟨u, hu, v, hv, he⟩ := mem_prod_iff.mp (hanti.1 a ha)
    have hcomp : ForcingCompatible P R q u ∧ ForcingCompatible P R q v := by
      rw [he] at hc
      exact (product_compatible_iff hq hq hu hv).mp hc
    have hl := h.comparable_of_compatible hu hq (hnodes a ha).1 hz
      (forcingCompatible_symm hcomp.1) (by simpa only [he, kpair.π₁_kpair] using (hforces a ha).1) hqz
    have hr := h.comparable_of_compatible hv hq (hnodes a ha).2 hz
      (forcingCompatible_symm hcomp.2) (by simpa only [he, kpair.π₂_kpair] using (hforces a ha).2.1) hqz
    have hlrank : rank ‘ (left a) ∈ rank ‘ z := hiz _ (hBi _
      (mem_union_iff.mpr (Or.inl ((repl_spec hL).mpr ⟨a, ha, rfl⟩))))
    have hrrank : rank ‘ (right a) ∈ rank ‘ z := hiz _ (hBi _
      (mem_union_iff.mpr (Or.inr ((repl_spec hU).mpr ⟨a, ha, rfl⟩))))
    have hlz := hl.resolve_right (fun hzl ↦ mem_irrefl _
      (h.rank_monotone z hz (left a) (hnodes a ha).1 hzl _ hlrank))
    have hrz := hr.resolve_right (fun hzr ↦ mem_irrefl _
      (h.rank_monotone z hz (right a) (hnodes a ha).2 hzr _ hrrank))
    exact (hforces a ha).2.2 (h.below_linear _ (hnodes a ha).1 _ (hnodes a ha).2 z hz hlz hrz)
  refine ⟨q, mem_sep_iff.mpr ⟨hq, ?_⟩, hqp⟩
  intro x hx y hy
  obtain ⟨hxT, r, hr, hrq, hrx⟩ := mem_sep_iff.mp hx
  obtain ⟨hyT, s, hs, hsq, hsy⟩ := mem_sep_iff.mp hy
  by_contra hxy
  have hrs : ⟨r, s⟩ₖ ∈ Split := by
    apply mem_sep_iff.mpr
    refine ⟨kpair_mem_iff.mpr ⟨hr, hs⟩, x, hxT, y, hyT, ?_⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hrx (And.intro hsy hxy)
  obtain ⟨a, ha, hcomp⟩ := hmax _ hrs
  apply hnone a ha
  apply forcingCompatible_of_stronger hQ (kpair_mem_iff.mpr ⟨hq, hq⟩)
    (kpair_mem_iff.mpr ⟨hr, hs⟩) (hanti.1 a ha)
  · exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hr, hs, hq, hq, hrq, hsq⟩
  · exact forcingCompatible_symm hcomp

end ZFVP.Schmerl
