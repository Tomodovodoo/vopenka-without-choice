import ZFVP.ModelTheory.ForcingSmallFunctions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingCheckedFunctionBoundFormula : SetTheorySemisentence 7 :=
  f“b P R o d X t. ∃ Y, (∀ y, y ∈ Y ↔ y ∈ d ∧ ∃ p ∈ P, ∃ x ∈ X,
    !checkedFunctionValueDecisionFormula P R o t p x y) ∧ b = !succ.dfn (!sUnion.dfn Y)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem small_forcing_checked_function_values_bounded {P R one δ X : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hX : X ∈ hierarchy δ)
    (τ : ForcingName P) :
    ∃ β ∈ δ, ∀ p ∈ P, ∀ x ∈ X, ∀ y ∈ δ,
      ForcesCheckedFunctionValue P R one τ.val p x y → y ∈ β := by
  let := hδ.1
  let g := {z ∈ (X ×ˢ P) ×ˢ δ ;
    ForcesCheckedFunctionValue P R one τ.val (kpair.π₂ (kpair.π₁ z))
      (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ z)}
  have hm (z y : V) : ⟨z, y⟩ₖ ∈ g ↔ z ∈ X ×ˢ P ∧ y ∈ δ ∧
      ForcesCheckedFunctionValue P R one τ.val (kpair.π₂ z) (kpair.π₁ z) y := by
    simp [g, and_assoc]
  have hf : g ∈ δ ^ domain g := by
    apply mem_function.intro
    · intro c hc
      obtain ⟨z, _, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hc).1
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hc, hy⟩
    · intro z hz
      obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
      refine ⟨y, hzy, fun w hzw ↦ ?_⟩
      exact forcesCheckedFunctionValue_unique hR ht τ.property
        ((hm z w).mp hzw).2.2 ((hm z y).mp hzy).2.2
  have hdsub : domain g ⊆ X ×ˢ P := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
    exact ((hm z y).mp hzy).1
  have hs : ∀ β ∈ δ, succ β ∈ δ := fun _ hb ↦ regularCardinal_succ_closed hδ.regular hb
  have hd : domain g ∈ hierarchy δ := subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs hX hP) hdsub
  have hn : NoLowRankCofinalMaps δ := fun _ ha _ ↦ hδ.no_rank_cofinalMap ha
  obtain ⟨β, hβ, hb⟩ := hn.map_bounded hd hf
  let := IsFunction.of_mem hf
  refine ⟨β, hβ, ?_⟩
  intro p hp x hx y hy hforce
  have hxy : ⟨⟨x, p⟩ₖ, y⟩ₖ ∈ g := (hm _ _).mpr
    ⟨kpair_mem_iff.mpr ⟨hx, hp⟩, hy, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hforce⟩
  exact value_eq_of_kpair_mem hxy ▸ hb _ (mem_domain_of_kpair_mem hxy)

noncomputable def forcingCheckedFunctionBound (P R one δ X τ : V) : V :=
  succ (⋃ˢ {y ∈ δ ; ∃ p ∈ P, ∃ x ∈ X, ForcesCheckedFunctionValue P R one τ p x y})

instance forcingCheckedFunctionBoundFormula_defined :
    Defined (fun v : Fin 7 → V ↦ v 0 = forcingCheckedFunctionBound (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      forcingCheckedFunctionBoundFormula :=
  ⟨fun v ↦ by
    simp [forcingCheckedFunctionBoundFormula, forcingCheckedFunctionBound]
    constructor
    · rintro ⟨Y, hY, he⟩
      have hY' : Y = {y ∈ v 4 ; ∃ p ∈ v 1, ∃ x ∈ v 5,
          ForcesCheckedFunctionValue (v 1) (v 2) (v 3) (v 6) p x y} := by
        apply mem_ext
        intro y
        simpa only [mem_sep_iff] using hY y
      exact hY' ▸ he
    · intro he
      exact ⟨_, fun y ↦ mem_sep_iff, he⟩⟩

instance forcingCheckedFunctionBound_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 6 → V ↦ forcingCheckedFunctionBound (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  forcingCheckedFunctionBoundFormula_defined.to_definable

theorem forcingCheckedFunctionBound_spec {P R one δ X : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hX : X ∈ hierarchy δ)
    (τ : ForcingName P) :
    forcingCheckedFunctionBound P R one δ X τ.val ∈ δ ∧
      ∀ p ∈ P, ∀ x ∈ X, ∀ y ∈ δ, ForcesCheckedFunctionValue P R one τ.val p x y →
        y ∈ forcingCheckedFunctionBound P R one δ X τ.val := by
  let := hδ.1
  let Y := {y ∈ δ ; ∃ p ∈ P, ∃ x ∈ X, ForcesCheckedFunctionValue P R one τ.val p x y}
  let := IsOrdinal.sUnion (fun y hy ↦ IsOrdinal.of_mem (mem_sep_iff.mp hy).1 : ∀ y ∈ Y, IsOrdinal y)
  obtain ⟨β, hβ, hb⟩ := small_forcing_checked_function_values_bounded hR ht hδ hP hX τ
  let := IsOrdinal.of_mem hβ
  have hsub : ⋃ˢ Y ⊆ β := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
    obtain ⟨hyδ, p, hp, x, hx, hf⟩ := mem_sep_iff.mp hy
    exact IsOrdinal.toIsTransitive.mem_trans hzy (hb p hp x hx y hyδ hf)
  refine ⟨regularCardinal_succ_closed hδ.regular (ordinal_mem_of_subset_mem hsub hβ), ?_⟩
  intro p hp x hx y hy hf
  let := IsOrdinal.of_mem hy
  change y ∈ succ (⋃ˢ Y)
  exact ordinal_mem_of_subset_mem (subset_sUnion_of_mem (mem_sep_iff.mpr ⟨hy, p, hp, x, hx, hf⟩))
    (show ⋃ˢ Y ∈ succ (⋃ˢ Y) by simp)

namespace ForcingContext

theorem checkedFunctionBound_values (A : ForcingContext V) {δ X : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hX : X ∈ hierarchy δ)
    (τ : ForcingName A.P) (hf : A.ofName τ ∈ A.check δ ^ A.check X) :
    ∀ a ∈ A.check X, (A.ofName τ) ‘ a ∈
      A.check (forcingCheckedFunctionBound A.P A.R A.one δ X τ.val) := by
  have hb := (forcingCheckedFunctionBound_spec A.order A.top hδ hP hX τ).2
  let := IsFunction.of_mem hf
  intro a ha
  obtain ⟨x, hx, rfl⟩ := (A.mem_check_iff X a).mp ha
  obtain ⟨y, hy, hey⟩ := (A.mem_check_iff δ _).mp
    (function_value_mem hf ((A.check_mem_iff x X).mpr hx))
  obtain ⟨p, hp, hpxy⟩ := (A.checkedFunctionValue_truth τ x y).mpr ⟨inferInstance, hey⟩
  rw [hey, A.check_mem_iff]
  exact hb p (A.generic.1.1 p hp) x hx y hy hpxy

end ForcingContext
end ZFVP
