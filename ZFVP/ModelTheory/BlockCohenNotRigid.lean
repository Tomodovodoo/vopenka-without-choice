import ZFVP.ModelTheory.BlockCohenModel
import ZFVP.SetTheory.RigidRelation
import ZFVP.SetTheory.InternalTranspositions

/-!
The set of blocks of the block Cohen symmetric model carries no rigid relation, so the rigid
relation principle fails in that model.

The argument is the forcing form of Theorem 5 of Hamkins and Palumbo, done without atoms and
without the Jech-Sochor transfer. A relation `R` on the blocks has a hereditarily symmetric name
supported by a finite set `E` of blocks. Two blocks `b` and `c` outside `E` can be swapped by a
block permutation that fixes every index of every block of `E` and moves the copy indices of a
given condition off themselves, so no condition of the generic filter can force that a pair of
blocks lies in `R` while its swap does not. Hence the transposition of `b` and `c` inside the
model is an automorphism of `R`, and it is not the identity.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The pair of the second and third variable lies in the first, and the pair of the fourth and
fifth does not. -/
def swapSplitFormula : SetTheorySemisentence 5 :=
  f“R x y u v. !kpair.dfn x y ∈ R ∧ ¬ !kpair.dfn u v ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_swapSplitFormula_assignment (v : Fin 5 → V) :
    swapSplitFormula.Evalb v ↔ ⟨v 1, v 2⟩ₖ ∈ v 0 ∧ ⟨v 3, v 4⟩ₖ ∉ v 0 := by
  simp [swapSplitFormula]

namespace BlockCohenModel

variable [Countable V] {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions ((ω : V) ×ˢ (ω : V)))
    (cohenOrder ((ω : V) ×ˢ (ω : V))) G)

omit [Countable V] in
/-- Equal indices give the same block. -/
theorem block_congr {a a' : V} (ha : a ∈ (ω : V)) (ha' : a' ∈ (ω : V)) (h : a = a') :
    block hG a ha = block hG a' ha' := by
  subst h; rfl

/-- No condition of the generic filter decides a pair of blocks into a relation with a
symmetric name while keeping the swapped pair out of it. -/
theorem no_split_pair (τ : (blockCohenContext G hG).Name)
    {E : V} (hEω : E ⊆ (ω : V))
    (hE : ∀ π ρ, IsBlockPermutation π ρ →
      (∀ a ∈ E, ∀ ξ ∈ (ω : V), π ‘ ⟨a, ξ⟩ₖ = ⟨a, ξ⟩ₖ) →
      nameAction (cohenPermutation ((ω : V) ×ˢ (ω : V)) π) τ.val = τ.val)
    {ρ : V} (hρ : IsInternalPermutation (ω : V) ρ) (hρfix : ∀ a ∈ E, ρ ‘ a = a)
    (hρout : ∀ a ∈ (ω : V), a ∉ E → ρ ‘ a ∉ E)
    {a₁ a₂ b₁ b₂ : V} (h1 : a₁ ∈ (ω : V)) (h2 : a₂ ∈ (ω : V))
    (hb1 : b₁ ∈ (ω : V)) (hb2 : b₂ ∈ (ω : V))
    (he1 : ρ ‘ a₁ = b₁) (he2 : ρ ‘ a₂ = b₂)
    (hi1 : ρ ‘ b₁ = a₁) (hi2 : ρ ‘ b₂ = a₂) :
    ¬ (⟨block hG a₁ h1, block hG a₂ h2⟩ₖ ∈ (blockCohenContext G hG).ofName τ ∧
        ⟨block hG b₁ hb1, block hG b₂ hb2⟩ₖ ∉ (blockCohenContext G hG).ofName τ) := by
  classical
  intro hsplit
  let S := blockCohenContext G hG
  let β : ∀ a : V, a ∈ (ω : V) → S.Name := fun a ha ↦ ⟨blockName a, blockName_hereditarilySymmetric ha⟩
  let v : Fin 5 → S.Name := ![τ, β a₁ h1, β a₂ h2, β b₁ hb1, β b₂ hb2]
  have heval : swapSplitFormula.Evalb (fun k ↦ S.ofName (v k)) :=
    (eval_swapSplitFormula_assignment _).mpr hsplit
  obtain ⟨q, hqG, hqforce⟩ := (S.formula_truth swapSplitFormula v).mp heval
  have hq : q ∈ cohenConditions ((ω : V) ×ˢ (ω : V)) := hG.1.1 q hqG
  obtain ⟨s, hs, hfresh⟩ :=
    exists_omega_shift (blockCopyIndices_subset hq) (blockCopyIndices_finite hq)
  have hπρ : IsBlockPermutation (blockShift E ρ s) ρ :=
    blockShift_isBlockPermutation hEω hρ hρfix hρout hs
  let a := cohenPermutation ((ω : V) ×ˢ (ω : V)) (blockShift E ρ s)
  have ha : IsForcingAutomorphism S.P S.R a := cohenPermutation_automorphism hπρ.1
  have haG : a ∈ S.Γ := (mem_blockCohenGroup a).mpr ⟨blockShift E ρ s, ρ, hπρ, rfl⟩
  have hτfix : nameAction a τ.val = τ.val :=
    hE _ ρ hπρ (fun d hd ξ hξ ↦ blockShift_value_mem hd (hEω d hd) hξ)
  have hβmove : ∀ (d : V) (hd : d ∈ (ω : V)), nameAction a (blockName d) = blockName (ρ ‘ d) :=
    fun d hd ↦ nameAction_blockName hπρ hd
  let w : Fin 5 → S.Name := ![τ, β b₁ hb1, β b₂ hb2, β a₁ h1, β a₂ h2]
  have hnames : (fun k ↦ nameAction a (v k).val) = fun k ↦ (w k).val := by
    funext k
    refine Fin.cases hτfix ?_ k
    intro k
    refine Fin.cases (show nameAction a (blockName a₁) = blockName b₁ by
      rw [hβmove a₁ h1, he1]) ?_ k
    intro k
    refine Fin.cases (show nameAction a (blockName a₂) = blockName b₂ by
      rw [hβmove a₂ h2, he2]) ?_ k
    intro k
    refine Fin.cases (show nameAction a (blockName b₁) = blockName a₁ by
      rw [hβmove b₁ hb1, hi1]) ?_ k
    intro k
    exact Fin.cases (show nameAction a (blockName b₂) = blockName a₂ by
      rw [hβmove b₂ hb2, hi2]) (fun l ↦ Fin.elim0 l) k
  have haqforce : a ‘ q ∈ symmetricForcingFormula S.P S.R S.Γ S.F swapSplitFormula
      (standardTuple (fun k ↦ (w k).val)) := by
    have hh := (symmetricForcingFormula_nameAction_iff S.order S.group S.normal haG
      swapSplitFormula (fun k ↦ (v k).val) (fun k ↦ (v k).property) hq).mpr hqforce
    simpa only [hnames] using hh
  obtain ⟨r, hr, hrq, hra⟩ := blockShift_compatible hq hfresh hEω hρ hρfix hρout hs
  have hra' : ⟨r, a ‘ q⟩ₖ ∈ S.R := by
    change ⟨r, (cohenPermutation ((ω : V) ×ˢ (ω : V)) (blockShift E ρ s)) ‘ q⟩ₖ
      ∈ cohenOrder ((ω : V) ×ˢ (ω : V))
    rw [cohenPermutation_value hq]
    exact hra
  obtain ⟨H, hH, hrH⟩ := exists_externalForcingGeneric S.order hr
  have hqH : q ∈ H := hH.1.2.2.1 r hrH q hq hrq
  have haqH : a ‘ q ∈ H := hH.1.2.2.1 r hrH (a ‘ q) (function_value_mem ha.1 hq) hra'
  let T := blockCohenContext H hH
  have hevalv : swapSplitFormula.Evalb (fun k ↦ T.ofName (v k)) :=
    (T.formula_truth swapSplitFormula v).mpr ⟨q, hqH, hqforce⟩
  have hevalw : swapSplitFormula.Evalb (fun k ↦ T.ofName (w k)) :=
    (T.formula_truth swapSplitFormula w).mpr ⟨a ‘ q, haqH, haqforce⟩
  have hv : ⟨T.ofName (β a₁ h1), T.ofName (β a₂ h2)⟩ₖ ∈ T.ofName τ ∧
      ⟨T.ofName (β b₁ hb1), T.ofName (β b₂ hb2)⟩ₖ ∉ T.ofName τ :=
    (eval_swapSplitFormula_assignment _).mp hevalv
  have hw : ⟨T.ofName (β b₁ hb1), T.ofName (β b₂ hb2)⟩ₖ ∈ T.ofName τ ∧
      ⟨T.ofName (β a₁ h1), T.ofName (β a₂ h2)⟩ₖ ∉ T.ofName τ :=
    (eval_swapSplitFormula_assignment _).mp hevalw
  exact hv.2 hw.1

/-- The blocks of the block Cohen symmetric model carry no rigid relation. -/
theorem blocks_not_hasRigidRelation : ¬ HasRigidRelation (blocks hG) := by
  classical
  rintro ⟨R, _, hRrig⟩
  obtain ⟨τ, hτ⟩ := (blockCohenContext G hG).ofName_surjective R
  have hτs : IsHereditarilySymmetricName (cohenConditions ((ω : V) ×ˢ (ω : V)))
      blockCohenGroup blockCohenFilter τ.val := τ.property
  obtain ⟨E, hEω, hEfin, hE⟩ := blockCohenName_blockSupport hτs
  obtain ⟨γ, hγ, hEγ⟩ := internallyFinite_naturals_bounded hEfin hEω
  have hoγ : IsOrdinal γ := IsOrdinal.of_mem hγ
  have hb : γ ∈ (ω : V) := hγ
  have hc : succ γ ∈ (ω : V) := ω_succ_closed hγ
  have hbE : γ ∉ E := fun h ↦ mem_irrefl _ (hEγ _ h)
  have hcE : succ γ ∉ E := fun h ↦
    mem_irrefl γ (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self γ) (hEγ _ h))
  have hbc : γ ≠ succ γ := by
    intro h
    have hm : γ ∈ succ γ := mem_succ_self γ
    rw [← h] at hm
    exact mem_irrefl γ hm
  -- the transposition of the two fresh blocks, as a permutation of `ω`
  set ρ : V := internalTransposition (ω : V) γ (succ γ) with hρdef
  have hρ : IsInternalPermutation (ω : V) ρ := internalTransposition_permutation hb hc
  have hρfix : ∀ d ∈ E, ρ ‘ d = d := fun d hd ↦
    internalTransposition_fixed (hEω d hd) (fun h ↦ hbE (h ▸ hd)) (fun h ↦ hcE (h ▸ hd))
  have hρout : ∀ d ∈ (ω : V), d ∉ E → ρ ‘ d ∉ E := by
    intro d hd hdE
    by_cases h1 : d = γ
    · rw [hρdef, internalTransposition_value hd, h1, transpositionValue_left]
      exact hcE
    · by_cases h2 : d = succ γ
      · rw [hρdef, internalTransposition_value hd, h2, transpositionValue_right]
        exact hbE
      · rw [hρdef, internalTransposition_value hd, transpositionValue_fixed h1 h2]
        exact hdE
  have hρmem : ∀ d ∈ (ω : V), ρ ‘ d ∈ (ω : V) := fun d hd ↦ function_value_mem hρ.1 hd
  have hρinv : ∀ d ∈ (ω : V), ρ ‘ (ρ ‘ d) = d := by
    intro d hd
    have hm : transpositionValue γ (succ γ) d ∈ (ω : V) := transpositionValue_mem hb hc hd
    rw [hρdef, internalTransposition_value hd, internalTransposition_value hm,
      transpositionValue_involutive]
  have hρb : ρ ‘ γ = succ γ := by rw [hρdef, internalTransposition_left hb]
  have hρc : ρ ‘ (succ γ) = γ := by rw [hρdef, internalTransposition_right hc]
  -- the relation cannot distinguish a pair of blocks from its swap
  have hswap : ∀ (a₁ a₂ b₁ b₂ : V) (h1 : a₁ ∈ (ω : V)) (h2 : a₂ ∈ (ω : V))
      (hb1 : b₁ ∈ (ω : V)) (hb2 : b₂ ∈ (ω : V)), ρ ‘ a₁ = b₁ → ρ ‘ a₂ = b₂ →
      (⟨block hG a₁ h1, block hG a₂ h2⟩ₖ ∈ R ↔ ⟨block hG b₁ hb1, block hG b₂ hb2⟩ₖ ∈ R) := by
    intro a₁ a₂ b₁ b₂ h1 h2 hb1 hb2 he1 he2
    have hi1 : ρ ‘ b₁ = a₁ := by rw [← he1, hρinv a₁ h1]
    have hi2 : ρ ‘ b₂ = a₂ := by rw [← he2, hρinv a₂ h2]
    constructor
    · intro hin
      by_contra hnin
      exact no_split_pair hG τ hEω hE hρ hρfix hρout h1 h2 hb1 hb2 he1 he2 hi1 hi2
        ⟨hτ ▸ hin, fun hh ↦ hnin (hτ ▸ hh)⟩
    · intro hin
      by_contra hnin
      exact no_split_pair hG τ hEω hE hρ hρfix hρout hb1 hb2 h1 h2 hi1 hi2 he1 he2
        ⟨hτ ▸ hin, fun hh ↦ hnin (hτ ▸ hh)⟩
  -- the transposition of the two fresh blocks, inside the model
  set f : (blockCohenContext G hG).Model :=
    internalTransposition (blocks hG) (block hG γ hb) (block hG (succ γ) hc) with hfdef
  have hfperm : IsInternalPermutation (blocks hG) f :=
    internalTransposition_permutation (block_mem_blocks hG γ hb) (block_mem_blocks hG (succ γ) hc)
  have hfval : ∀ (d : V) (hd : d ∈ (ω : V)) (hd' : ρ ‘ d ∈ (ω : V)),
      f ‘ (block hG d hd) = block hG (ρ ‘ d) hd' := by
    intro d hd hd'
    by_cases h1 : d = γ
    · subst h1
      rw [hfdef, internalTransposition_left (block_mem_blocks hG d hd)]
      exact block_congr hG hc hd' hρb.symm
    · by_cases h2 : d = succ γ
      · subst h2
        rw [hfdef, internalTransposition_right (block_mem_blocks hG (succ γ) hc)]
        exact block_congr hG hb hd' hρc.symm
      · rw [hfdef, internalTransposition_fixed (block_mem_blocks hG d hd)
          (block_ne hG hd hb h1) (block_ne hG hd hc h2)]
        refine block_congr hG hd hd' ?_
        rw [hρdef, internalTransposition_value hd, transpositionValue_fixed h1 h2]
  have hauto : IsAutomorphismOf (blocks hG) R f := by
    refine ⟨hfperm.1, hfperm.2.1, hfperm.2.2, ?_⟩
    intro x hx y hy
    obtain ⟨a₁, h1, rfl⟩ := (mem_blocks_iff hG x).mp hx
    obtain ⟨a₂, h2, rfl⟩ := (mem_blocks_iff hG y).mp hy
    rw [hfval a₁ h1 (hρmem a₁ h1), hfval a₂ h2 (hρmem a₂ h2)]
    exact hswap a₁ a₂ (ρ ‘ a₁) (ρ ‘ a₂) h1 h2 (hρmem a₁ h1) (hρmem a₂ h2) rfl rfl
  have hfix : f ‘ (block hG γ hb) = block hG γ hb :=
    hRrig f hauto _ (block_mem_blocks hG γ hb)
  rw [hfval γ hb (hρmem γ hb)] at hfix
  exact block_ne hG (hρmem γ hb) hb (by rw [hρb]; exact fun h ↦ hbc h.symm) hfix

/-- The rigid relation principle fails in the block Cohen symmetric model. -/
theorem blockCohen_model_not_rigidRelationPrinciple :
    ¬ RigidRelationPrinciple (blockCohenContext G hG).Model :=
  fun h ↦ blocks_not_hasRigidRelation hG (h (blocks hG))

end BlockCohenModel
end ZFVP
