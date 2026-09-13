import ZFVP.SetTheory.LevyUpperPermutations
import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.ModelTheory.LevyProductEquivalence
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.MembershipIso

/-! Truth of statements about ground parameters in a weakly homogeneous extension is decided by
the top condition. For the Levy collapse: truth in `V[G]` of statements about elements of
`V[G_β]` is decided in `V[G_β]` by the top of the upper collapse `Coll(ω,[β,κ))`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem one_mem_G (A : ForcingContext V) : A.one ∈ A.G := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact A.generic.1.2.2.1 p hp A.one A.top.1 (A.top.2 p (A.generic.1.1 p hp))

/-- In a weakly homogeneous extension, a statement about checks holds exactly when the top forces it. -/
theorem truth_iff_top_forces (A : ForcingContext V) (hhom : IsWeaklyHomogeneous A.P A.R A.one)
    {n : ℕ} (φ : SetTheorySemisentence n) (a : Fin n → V) :
    φ.Evalb (fun i ↦ A.check (a i)) ↔
      A.one ∈ forcingFormula A.P A.R φ (standardTuple (fun i ↦ checkName A.one (a i))) := by
  have h := A.formula_truth φ (fun i ↦ ⟨checkName A.one (a i), checkName_isName A.top.1 (a i)⟩)
  change φ.Evalb (fun i ↦ A.check (a i)) ↔ _ at h
  rw [h]
  constructor
  · rintro ⟨p, _, hp⟩
    exact forced_by_top_of_homogeneous A.order A.top hhom φ a hp
  · intro h1
    exact ⟨A.one, A.one_mem_G, h1⟩

end ForcingContext

section

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

theorem levyProductConditions_eq :
    levyProductConditions β hβ hG =
      levyCollapseAbove ((levySubContext β hβ hG).check κ) ((levySubContext β hβ hG).check β) :=
  (levySubContext β hβ hG).checkEmbedding.map_levyCollapseAbove κ β

theorem levyProductOrder_eq :
    levyProductOrder β hβ hG = restrictedOrder (levyOrder ((levySubContext β hβ hG).check κ))
      (levyCollapseAbove ((levySubContext β hβ hG).check κ) ((levySubContext β hβ hG).check β)) := by
  unfold levyProductOrder
  rw [levyProductConditions_eq]
  congr 1
  exact (levySubContext β hβ hG).checkEmbedding.map_levyOrder κ

theorem levyProductContext_one_eq : (levyProductContext β hβ hG).one = ∅ :=
  (levySubContext β hβ hG).checkEmbedding.map_empty

/-- The upper collapse over `V[G_β]` is weakly homogeneous. -/
theorem levyProductContext_homogeneous :
    IsWeaklyHomogeneous (levyProductContext β hβ hG).P (levyProductContext β hβ hG).R
      (levyProductContext β hβ hG).one := by
  change IsWeaklyHomogeneous (levyProductConditions β hβ hG) (levyProductOrder β hβ hG)
    ((levySubContext β hβ hG).check ∅)
  have h0 : (levySubContext β hβ hG).check ∅ = ∅ := (levySubContext β hβ hG).checkEmbedding.map_empty
  rw [levyProductConditions_eq, levyProductOrder_eq, h0]
  exact levyCollapseAbove_homogeneous (((levySubContext β hβ hG).checkEmbedding.subset_iff _ _).mpr hβ)

/-- Truth in the two-step extension of statements about elements of `V[G_β]` is decided by the
top of the upper collapse. -/
theorem levyProduct_truth_iff_top {n : ℕ} (φ : SetTheorySemisentence n)
    (a : Fin n → (levySubContext β hβ hG).Model) :
    φ.Evalb (fun i ↦ (levyProductContext β hβ hG).check (a i)) ↔
      (levyProductContext β hβ hG).one ∈ forcingFormula (levyProductContext β hβ hG).P
        (levyProductContext β hβ hG).R φ
        (standardTuple (fun i ↦ checkName (levyProductContext β hβ hG).one (a i))) :=
  (levyProductContext β hβ hG).truth_iff_top_forces (levyProductContext_homogeneous β hβ hG) φ a

/-- Truth in `V[G]` of statements about elements of `V[G_β]` is decided in `V[G_β]` by the top of
the upper collapse. -/
theorem levy_truth_iff_top {n : ℕ} (φ : SetTheorySemisentence n)
    (τ : Fin n → ForcingName (levySubContext β hβ hG).P) :
    φ.Evalb (fun i ↦ (levyContext κ hG).ofName (levySubNameLift β hβ hG (τ i))) ↔
      (levyProductContext β hβ hG).one ∈ forcingFormula (levyProductContext β hβ hG).P
        (levyProductContext β hβ hG).R φ
        (standardTuple (fun i ↦ checkName (levyProductContext β hβ hG).one
          ((levySubContext β hβ hG).ofName (τ i)))) := by
  rw [← levyProduct_truth_iff_top]
  have he := eval_membershipIso (levyProductEquiv β hβ hG) (levyProductEquiv_mem_iff β hβ hG) φ
    (fun i ↦ (levyContext κ hG).ofName (levySubNameLift β hβ hG (τ i))) Empty.elim
  have hfun : (levyProductEquiv β hβ hG ∘ fun i ↦ (levyContext κ hG).ofName (levySubNameLift β hβ hG (τ i))) =
      fun i ↦ (levyProductContext β hβ hG).check ((levySubContext β hβ hG).ofName (τ i)) :=
    funext (fun i ↦ levyProductEquiv_lift β hβ hG (τ i))
  have hempty : (levyProductEquiv β hβ hG ∘ (Empty.elim : Empty → (levyContext κ hG).Model)) = Empty.elim :=
    funext (fun x ↦ x.elim)
  rw [hfun, hempty] at he
  exact he

end

end ZFVP
