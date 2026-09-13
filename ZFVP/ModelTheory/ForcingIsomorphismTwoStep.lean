import ZFVP.ModelTheory.ForcingIsomorphismFormula
import ZFVP.SetTheory.TwoStepForcing
import ZFVP.SetTheory.WoodinSeedOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepNames_isName {P N t τ : V} (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hτ : τ ∈ twoStepNames N t) : IsForcingName P τ := by
  rcases mem_union_iff.mp hτ with hτ | hτ
  · obtain ⟨p, hp⟩ := mem_domain_iff.mp hτ
    exact forcingName_subname hN hp
  · exact (mem_singleton_iff.mp hτ).symm ▸ ht

theorem nameAction_twoStepNames {P N t τ f : V} (hN : IsForcingName P N)
    (hτ : τ ∈ twoStepNames N t) : nameAction f τ ∈ twoStepNames (nameAction f N) (nameAction f t) := by
  rcases mem_union_iff.mp hτ with hτ | hτ
  · obtain ⟨p, hp⟩ := mem_domain_iff.mp hτ
    exact mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem
      ((mem_nameAction_iff hN f _).mpr ⟨τ, p, hp, rfl⟩)))
  · have he := mem_singleton_iff.mp hτ
    subst τ
    exact mem_union_iff.mpr (Or.inr (by simp))

noncomputable def twoStepNameAction (f z : V) : V :=
  ⟨f ‘ (kpair.π₁ z), nameAction f (kpair.π₂ z)⟩ₖ

instance twoStepNameAction_definable : ℒₛₑₜ-function₂[V] twoStepNameAction := by
  unfold twoStepNameAction
  definability

theorem twoStepNameAction_mem {P R Q S N t f x : V}
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions P R N t) :
    twoStepNameAction f x ∈ twoStepConditions Q S (nameAction f N) (nameAction f t) := by
  obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hx
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair]
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr
    ⟨function_value_mem hf.1 hp, nameAction_twoStepNames hN hτ,
      atomicMembership_isomorphism_forward hf (twoStepNames_isName hN ht hτ) hN hm⟩

theorem twoStepNameAction_inverse_mem {P R Q S N t f x : V}
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions Q S (nameAction f N) (nameAction f t)) :
    twoStepNameAction (converseGraph f) x ∈ twoStepConditions P R N t := by
  have hh := twoStepNameAction_mem hf.inverse (nameAction_isName hf.1 hN) (nameAction_isName hf.1 ht) hx
  simpa only [hf.name_inverse_cancel hN, hf.name_inverse_cancel ht] using hh

theorem twoStepNameAction_inverse_cancel {P R Q S N t f x : V}
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions P R N t) :
    twoStepNameAction (converseGraph f) (twoStepNameAction f x) = x := by
  obtain ⟨p, hp, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hx
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair,
    hf.inverse_value hp, hf.name_inverse_cancel (twoStepNames_isName hN ht hτ)]

theorem twoStepNameAction_cancel_inverse {P R Q S N t f x : V}
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions Q S (nameAction f N) (nameAction f t)) :
    twoStepNameAction f (twoStepNameAction (converseGraph f) x) = x := by
  obtain ⟨p, hp, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hx
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair,
    hf.value_inverse hp, hf.name_cancel_inverse
      (twoStepNames_isName (nameAction_isName hf.1 hN) (nameAction_isName hf.1 ht) hτ)]

theorem twoStepNameAction_order_iff {P R Q S N T t f x y : V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f)
    (hN : IsForcingName P N) (hT : IsForcingName P T) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions P R N t) (hy : y ∈ twoStepConditions P R N t) :
    ⟨twoStepNameAction f x, twoStepNameAction f y⟩ₖ ∈
      twoStepOrder Q S (nameAction f N) (nameAction f T) (nameAction f t) ↔
      ⟨x, y⟩ₖ ∈ twoStepOrder P R N T t := by
  have hfx := twoStepNameAction_mem hf hN ht hx
  have hfy := twoStepNameAction_mem hf hN ht hy
  rw [kpair_mem_twoStepOrder, kpair_mem_twoStepOrder]
  simp only [hx, hy, hfx, hfy, true_and]
  obtain ⟨p, hp, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hx
  obtain ⟨q, hq, σ, hσ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hy
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr (hf.2.2.2 p hp q hq).symm
  have hh := forcingFormula_isomorphism_iff hR hS hf boundedPairMemberFormula ![T, τ, σ]
    (fun i ↦ Fin.cases hT (fun j ↦ Fin.cases (twoStepNames_isName hN ht hτ)
      (fun k ↦ Fin.cases (twoStepNames_isName hN ht hσ) (fun l ↦ Fin.elim0 l) k) j) i) hp
  have he : (fun i : Fin 3 ↦ nameAction f (![T, τ, σ] i)) =
      ![nameAction f T, nameAction f τ, nameAction f σ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [he] at hh
  exact hh

noncomputable def twoStepIsomorphismMap (P R N t f : V) : V :=
  definableGraph (twoStepConditions P R N t) (twoStepNameAction f) (by definability)

theorem twoStep_isomorphism {P R Q S N T t f : V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f)
    (hN : IsForcingName P N) (hT : IsForcingName P T) (ht : IsForcingName P t) :
    IsForcingIsomorphism (twoStepConditions P R N t) (twoStepOrder P R N T t)
      (twoStepConditions Q S (nameAction f N) (nameAction f t))
      (twoStepOrder Q S (nameAction f N) (nameAction f T) (nameAction f t))
      (twoStepIsomorphismMap P R N t f) := by
  apply forcingIsomorphism_of_inverse (twoStepNameAction f) (twoStepNameAction (converseGraph f))
  · exact fun _ hx ↦ twoStepNameAction_mem hf hN ht hx
  · exact fun _ hx ↦ twoStepNameAction_inverse_mem hf hN ht hx
  · exact fun _ hx ↦ twoStepNameAction_inverse_cancel hf hN ht hx
  · exact fun _ hx ↦ twoStepNameAction_cancel_inverse hf hN ht hx
  · exact fun _ hx _ hy ↦ (twoStepNameAction_order_iff hR hS hf hN hT ht hx hy).symm

theorem twoStepIsomorphismMap_projection {P R Q S N t f x : V}
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) (ht : IsForcingName P t)
    (hx : x ∈ twoStepConditions P R N t) :
    (twoStepProjection Q S (nameAction f N) (nameAction f t)) ‘
        ((twoStepIsomorphismMap P R N t f) ‘ x) =
      f ‘ ((twoStepProjection P R N t) ‘ x) := by
  rw [twoStepIsomorphismMap, value_definableGraph _ _ _ hx,
    twoStepProjection_value (twoStepNameAction_mem hf hN ht hx), twoStepProjection_value hx]
  simp only [twoStepNameAction, kpair.π₁_kpair]

theorem twoStepIsomorphismMap_section {P R Q S N t f p : V}
    (hf : IsForcingIsomorphism P R Q S f) (hp : p ∈ P)
    (hsection : ⟨p, t⟩ₖ ∈ twoStepConditions P R N t) :
    (twoStepIsomorphismMap P R N t f) ‘ ((twoStepSection P t) ‘ p) =
      (twoStepSection Q (nameAction f t)) ‘ (f ‘ p) := by
  rw [twoStepSection_value hp, twoStepIsomorphismMap, value_definableGraph _ _ _ hsection,
    twoStepSection_value (function_value_mem hf.1 hp)]
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair]

theorem twoStepIsomorphismMap_value {P R N t f x : V}
    (hx : x ∈ twoStepConditions P R N t) :
    (twoStepIsomorphismMap P R N t f) ‘ x =
      ⟨f ‘ (kpair.π₁ x), nameAction f (kpair.π₂ x)⟩ₖ := by
  exact value_definableGraph _ _ _ hx

theorem twoStepIsomorphismMap_top {P R N f one top : V}
    (hx : ⟨one, ∅⟩ₖ ∈ twoStepConditions P R N ∅) (hf : f ‘ one = top) :
    (twoStepIsomorphismMap P R N ∅ f) ‘ ⟨one, ∅⟩ₖ = ⟨top, ∅⟩ₖ := by
  rw [twoStepIsomorphismMap_value hx, kpair.π₁_kpair, kpair.π₂_kpair, nameAction_empty, hf]

theorem twoStepIsomorphismMap_replace {P R N t f x b : V}
    (hx : x ∈ twoStepConditions P R N t)
    (hb : ⟨b, kpair.π₂ x⟩ₖ ∈ twoStepConditions P R N t) :
    (twoStepIsomorphismMap P R N t f) ‘ ⟨b, kpair.π₂ x⟩ₖ =
      ⟨f ‘ b, kpair.π₂ ((twoStepIsomorphismMap P R N t f) ‘ x)⟩ₖ := by
  rw [twoStepIsomorphismMap_value hb, twoStepIsomorphismMap_value hx]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

end ZFVP
