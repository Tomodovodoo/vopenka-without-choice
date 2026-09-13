import ZFVP.ModelTheory.LocalSelectedUnionBound
import ZFVP.ModelTheory.TwoStepSelectedUnion
import ZFVP.ModelTheory.SuccessorForcingLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V)

/-- A decided selected value is contained in the union, independently of descent. -/
theorem selectedName_subset_union {C D H d : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {X i : A.Model} (hf : A.ofName f ∈ A.check D ^ X)
    (hi : i ∈ X) (hd : d ∈ D) (he : (A.ofName f) ‘ i = A.check d) :
    A.ofName ⟨H ‘ d, hC _ (function_value_mem hH hd)⟩ ⊆
      A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val,
        forcingSelectedUnion_isName _ _ _ _ _ _⟩ := by
  rw [A.forcingSelectedUnion_eq_union_range hC hH f hf]
  have hs := compose_function
    (compose_function hf ((A.check_function_iff H D C).mpr hH))
    (A.evaluationGraph_mem_function C hC)
  intro x hx
  apply mem_sUnion_iff.mpr
  refine ⟨_, value_mem_range hs hi, ?_⟩
  rwa [A.selectedEvaluation_value hC hH (A.ofName f) hf hi hd he]

theorem selectedName_subset_localUnion {C D H d δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {X i : A.Model} (hf : A.ofName f ∈ A.check D ^ X)
    (hi : i ∈ X) (hd : d ∈ D) (he : (A.ofName f) ‘ i = A.check d)
    (hr : A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val,
      forcingSelectedUnion_isName _ _ _ _ _ _⟩ ∈ hierarchy (A.check δ)) :
    A.ofName ⟨H ‘ d, hC _ (function_value_mem hH hd)⟩ ⊆
      A.ofName ⟨forcingLocalCanonicalName A.P A.R A.one δ p
        (forcingSelectedUnion A.P A.R A.one C H f.val),
        forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ := by
  rw [A.localCanonicalName_value hδ hP hp
    ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ hr]
  exact A.selectedName_subset_union hC hH f hf hi hd he

end ForcingContext

theorem successorForcingLift_tail (L a b : V) :
    kpair.π₂ (successorForcingLiftValue L a b) = kpair.π₂ a := by
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₂_kpair]

end ZFVP
