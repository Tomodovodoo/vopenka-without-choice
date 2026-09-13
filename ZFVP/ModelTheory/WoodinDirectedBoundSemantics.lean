import ZFVP.ModelTheory.WoodinDirectedNormalization
import ZFVP.ModelTheory.WoodinBoundInvariantSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSeparativeDirectedFormula : SetTheorySemisentence 4 :=
  f“P R α f. !boundedFunctionFormula f α P ∧ ∃ S, !forcingSeparativeOrderFormula S P R ∧
    ∀ i ∈ α, ∀ j ∈ α, ∃ k ∈ α,
      !kpair.dfn (!value.dfn f k) (!value.dfn f i) ∈ S ∧
      !kpair.dfn (!value.dfn f k) (!value.dfn f j) ∈ S”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSeparativeDirectedFormula_defined :
    Defined (fun v : Fin 4 → V ↦ IsForcingDirectedFamily (v 0)
      (forcingSeparativeOrder (v 0) (v 1)) (v 2) (v 3)) forcingSeparativeDirectedFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeDirectedFormula, IsForcingDirectedFamily]⟩

def ForcesWoodinQuotientDirectedFamily (θ i p f α : V) : Prop :=
  let s := kpair.π₁ (woodinIterationRec i)
  let B := (forcingCodeP s) ‘ i
  let R := (forcingCodeR s) ‘ i
  let b := (forcingCodet s) ‘ i
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let U := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
  let π := forcingThreadCoordinate D i
  p ∈ forcingFormula B R forcingSeparativeDirectedFormula
    (standardTuple ![projectionQuotientName D π b, projectionQuotientOrderName U π b, checkName b α, f])

namespace ForcingContext

theorem projectionQuotient_sequence_directed (A : ForcingContext V) {Q S T U π τ ρ : V}
    {f α : A.Model}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (hf : IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α f) :
    IsForcingDirectedFamily (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α
      (compose f (A.check ρ)) := by
  rw [A.projectionQuotient_sequence_eq hπ hτ hρ.maps he hf.1]
  exact (A.projectionQuotient_projection hπ hτ hρ he).separative_directed_compose hf

theorem projectionQuotient_name_directed (A : ForcingContext V) {Q S T U π τ ρ : V}
    {α : A.Model}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) (f : ForcingName A.P)
    (hf : IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α (A.ofName f)) :
    IsForcingDirectedFamily (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α
      (A.ofName ⟨forcingCompositionName A.P A.R f.val (checkName A.one ρ),
        forcingCompositionName_isName _ _ _ _⟩) := by
  rw [A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName A.top.1 ρ⟩]
  exact A.projectionQuotient_sequence_directed hπ hτ hρ he hf

theorem projectionQuotient_directed_of_forced (A : ForcingContext V)
    {Q S π α p : V} (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (f : ForcingName A.P) (hp : p ∈ A.G)
    (hf : p ∈ forcingFormula A.P A.R forcingSeparativeDirectedFormula
      (standardTuple ![projectionQuotientName Q π A.one, projectionQuotientOrderName S π A.one,
        checkName A.one α, f.val])) :
    IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
      (A.check α) (A.ofName f) := by
  let QN : ForcingName A.P := ⟨projectionQuotientName Q π A.one, projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName S π A.one, projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  have ht := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeDirectedFormula
    ![QN, SN, ⟨checkName A.one α, checkName_isName A.top.1 α⟩, f]).mpr ⟨p, hp, hf⟩)
  change IsForcingDirectedFamily (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
    (A.check α) (A.ofName f) at ht
  rwa [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at ht

end ForcingContext
end ZFVP
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j)) (kpair.π₂ (woodinIterationRec j)))
include hs

theorem ForcingContext.woodinCoordinate_directed {i j α : V}
    (A : ForcingContext V) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    [IsOrdinal α] (f : ForcingName A.P)
    (hf : IsForcingDirectedFamily
      (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
      (A.check α) (A.ofName f)) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
    IsForcingDirectedFamily
      (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
        ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
      (forcingSeparativeOrder
        (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
        (A.projectionQuotientOrder ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))) (A.check α) (A.ofName μ) := by
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hπ := (woodinInverseCoordinate_split hs hi).projection
  have hτ := hc.system.projection hi hj hij
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
    woodinIterationPrefix_order_value hs hi (mem_succ_self i), ← hP, ← hR] at hπ hτ
  have hρ := (woodinInverseCoordinate_split hs hj).projection
  have he : ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘
        ((forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j) ‘ d) =
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ d := by
    intro d hd
    rw [forcingThreadCoordinate_value hd, forcingThreadCoordinate_value hd]
    exact woodinInverseThread_project hs hi hj hij hd
  have ht := A.projectionQuotient_name_directed hπ.maps hτ.maps hρ he f hf
  simpa only [woodinBoundCoordinateName, ← hP, ← hR, ← ho] using ht

end ZFVP
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ i p α j : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
include hs hi

theorem woodinQuotientDirectedFamily_semantics
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G) :
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    IsForcingDirectedFamily
      (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
      (A.check α) (A.ofName f) := by
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hi).code.system.order.preorder i (mem_succ_self i),
    (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
  have hπ := (woodinInverseCoordinate_split hs hi).projection
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)] at hπ
  have h0 : (∅ : V) ∈ θ := by
    let := IsOrdinal.of_mem hi
    rcases IsOrdinal.subset_iff.mp (empty_subset i) with he | he
    · exact he.symm ▸ hi
    · exact IsOrdinal.toIsTransitive.mem_trans he hi
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hD := (hc.system.inverseColumn h0 hc.subset_universe).order.preorder
  exact A.projectionQuotient_directed_of_forced hπ hD f hpG hf

end ZFVP
