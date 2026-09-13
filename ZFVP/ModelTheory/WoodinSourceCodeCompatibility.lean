import ZFVP.ModelTheory.WoodinSourceGenericProjection
import ZFVP.ModelTheory.ForcingCanonicalTransport
import ZFVP.ModelTheory.WoodinSourceSeedLimitMaps
import ZFVP.ModelTheory.WoodinSourceInvariant
import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.WoodinSourceEndpoint
import ZFVP.ModelTheory.WoodinSourceLimits
import ZFVP.ModelTheory.WoodinSourceLimitMaps
import ZFVP.ModelTheory.WoodinSourceLimitReplacement
import ZFVP.ModelTheory.WoodinSourceCompletedInverse
import ZFVP.ModelTheory.WoodinSourceCompletedSections
import ZFVP.ModelTheory.WoodinSourceCompletedReplacement
import ZFVP.SetTheory.WoodinSeedPrefix
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Stage reindexing and explicit limit maps, including seed and positive
projection, section and replacement laws, least-cutoff equality, and canonical
name and generic transport. -/
structure WoodinSourceCodeCompatibility (θ s K : V) [IsOrdinal θ] : Prop where
  code    :
    (IsForcingIterationCode (woodinSourceIndex θ) (woodinSourceCode θ s) )
  stage {α : V}  (hα : α ∈ θ) :
    (woodinIterationStage (woodinSourceCode θ s) (woodinSourceCardinals θ K) (woodinSourceIndex α) =
      woodinIterationStage s K α )
  seed   :
    (woodinIterationStage (woodinSourceCode θ s) (woodinSourceCardinals θ K) ∅ = woodinSeedStage )
  projection {α β : V}  (hα : α ∈ θ) (hβ : β ∈ θ) :
    ((forcingCodeπ (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeπ s) ‘ ⟨α, β⟩ₖ )
  sectionMap {α β : V}  (hα : α ∈ θ) (hβ : β ∈ θ) :
    ((forcingCodeE (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeE s) ‘ ⟨α, β⟩ₖ )
  replacement {α β : V}  (hα : α ∈ θ) (hβ : β ∈ θ) :
    ((forcingCodeL (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeL s) ‘ ⟨α, β⟩ₖ )
  cardinal {α : V}  (hα : α ∈ θ) :
    ((woodinSourceCardinals θ K) ‘ (woodinSourceIndex α) = K ‘ α )
  quotientClosure {i j η : V}
    (hi : i ∈ θ) (hj : j ∈ θ) :
    (IterationQuotientClosedBelow (woodinSourceCode θ s) (woodinSourceIndex i) (woodinSourceIndex j) η ↔
      IterationQuotientClosedBelow s i j η )
  rawInverse
     :
    (IsForcingIsomorphism (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
      (forcingInverseCodeOrder (woodinSourceIndex θ) (woodinSourceCode θ s))
      (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) )
  direct
     (hzero : (∅ : V) ∈ θ) :
    (IsForcingIsomorphism
      ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) )
  rawTop
     (hzero : (∅ : V) ∈ θ) :
    (woodinInsertSeed θ (forcingInverseCodeTop θ s) ∅ =
      forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) )
  rawProjection {α f : V}
     (hα : α ∈ θ) (hf : f ∈ forcingInverseCodePoset θ s) :
    (((forcingLimitProjectionColumn (woodinSourceIndex θ)
        (forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex α)) ‘
        ((woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘ f) =
      ((forcingLimitProjectionColumn θ (forcingInverseCodePoset θ s)) ‘ α) ‘ f )
  directProjection {α f : V}
     (hzero : (∅ : V) ∈ θ) (hα : α ∈ θ)
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ) :
    (((forcingLimitProjectionColumn (woodinSourceIndex θ)
        ((forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘
          (woodinSourceIndex θ))) ‘ (woodinSourceIndex α)) ‘
        ((woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘ f) =
      ((forcingLimitProjectionColumn θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘ α) ‘ f )
  rawSection {k p : V}
     (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    ((woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘
        (((forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ k) ‘ p) =
      ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘
          (woodinSourceIndex k)) ‘ p )
  directSection {k p : V}
     (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    ((woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘
        (((forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ k) ‘ p) =
      ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘
          (woodinSourceIndex k)) ‘ p )
  rawReplacement {f i b : V}
     (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hf : f ∈ forcingInverseCodePoset θ s) (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    (
    let C := forcingInverseCodePoset θ s
    let D := forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s)
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) ‘ i) ‘ ⟨f, b⟩ₖ) =
      ((forcingLimitLiftColumn D (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘
          (woodinSourceIndex i)) ‘ ⟨(woodinSeedThreadMap θ C) ‘ f, b⟩ₖ )
  directReplacement {f i b : V}
     (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    (
    let C := (forcingCodeP (forcingDirectCode θ s)) ‘ θ
    let D := (forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘
      (woodinSourceIndex θ)
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) ‘ i) ‘ ⟨f, b⟩ₖ) =
      ((forcingLimitLiftColumn D (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘
          (woodinSourceIndex i)) ‘ ⟨(woodinSeedThreadMap θ C) ‘ f, b⟩ₖ )
  completed
     (hzero : (∅ : V) ∈ θ) (γ : V) :
    (
    let c := forcingInverseSourceCutoff θ s γ
    let s' := woodinSourceCode θ s
    let θ' := woodinSourceIndex θ
    let c' := forcingInverseSourceCutoff θ' s' γ
    let z := forcingInverseSourceCollapseCode θ s c γ
    let z' := forcingInverseSourceCollapseCode θ' s' c' γ
    IsForcingIsomorphism ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ)
      ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s γ) )
  completedProjection {i x : V}
     (hzero : (∅ : V) ∈ θ) (hi : i ∈ θ) (γ : V)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    ((forcingCodeπ z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘ ((woodinSourceInverseCollapseMap θ s γ) ‘ x) =
      ((forcingCodeπ z) ‘ ⟨i, θ⟩ₖ) ‘ x )
  completedSection {i p : V}
     (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeE z) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ((forcingCodeE z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘ p )
  completedReplacement {i x b : V}
     (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ)
    (hle : ⟨b, (kpair.π₁ x) ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeL z) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ) =
      ((forcingCodeL z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘
        ⟨(woodinSourceInverseCollapseMap θ s γ) ‘ x, b⟩ₖ )
  seedProjection {C f : V}
    (hC : C ⊆ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
    (hf : f ∈ C) :
    (((forcingLimitProjectionColumn (woodinSourceIndex θ) C) ‘ ∅) ‘ f = ∅ )
  seedSection   :
    (((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
      (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘ ∅) ‘ ∅ =
        forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) )
  seedReplacement {C f : V}
    (hC : C ⊆ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
    (hf : f ∈ C) :
    (((forcingLimitLiftColumn C (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
      (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘ ∅) ‘ ⟨f, ∅⟩ₖ = f )
  completedSeedProjection {ζ γ x : V}
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ (woodinSourceIndex θ)) :
    (((forcingCodeπ (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ x = ∅ )
  completedSeedSection {ζ γ : V}
     :
    (((forcingCodeE (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ ∅ =
      ⟨forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s), ∅⟩ₖ )
  completedSeedReplacement {ζ γ x : V}
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ (woodinSourceIndex θ)) :
    (((forcingCodeL (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ ⟨x, ∅⟩ₖ = x )
  rawTopValue
     (hzero : (∅ : V) ∈ θ) :
    ((woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘ (forcingInverseCodeTop θ s) =
      forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) )
  rawCutoff
     (hzero : (∅ : V) ∈ θ) (γ : V) :
    (forcingInverseSourceCutoff θ s γ =
      forcingInverseSourceCutoff (woodinSourceIndex θ) (woodinSourceCode θ s) γ )
  rawTransport
     :
    (IsCanonicalForcingTransport (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
      (forcingInverseCodeOrder (woodinSourceIndex θ) (woodinSourceCode θ s))
      (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) )
  directTransport
     (hzero : (∅ : V) ∈ θ) :
    (IsCanonicalForcingTransport
      ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) )
  completedTransport
     (hzero : (∅ : V) ∈ θ) (γ : V) :
    (
    let c := forcingInverseSourceCutoff θ s γ
    let s' := woodinSourceCode θ s
    let θ' := woodinSourceIndex θ
    let c' := forcingInverseSourceCutoff θ' s' γ
    let z := forcingInverseSourceCollapseCode θ s c γ
    let z' := forcingInverseSourceCollapseCode θ' s' c' γ
    IsCanonicalForcingTransport ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ)
      ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s γ) )
  rawGenericProjection {i : V} 
     (hi : i ∈ θ) {G : Set V}
    (hG : IsExternalForcingFilter (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) G) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let P := forcingInverseCodePoset θ s
    let P' := forcingInverseCodePoset θ' s'
    let G' := forcingProjectionGeneric P' (forcingInverseCodeOrder θ' s') (woodinSeedThreadMap θ P) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingLimitProjectionColumn θ' P') ‘ (woodinSourceIndex i)) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingLimitProjectionColumn θ P) ‘ i) G )
  directGenericProjection {i : V} 
     (hi : i ∈ θ) {G : Set V}
    (hG : IsExternalForcingFilter ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ) G) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingDirectCode θ s
    let z' := forcingDirectCode θ' s'
    let P := (forcingCodeP z) ‘ θ
    let P' := (forcingCodeP z') ‘ θ'
    let G' := forcingProjectionGeneric P' ((forcingCodeR z') ‘ θ') (woodinSeedThreadMap θ P) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingLimitProjectionColumn θ' P') ‘ (woodinSourceIndex i)) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingLimitProjectionColumn θ P) ‘ i) G )
  completedGenericProjection {i : V} 
     (hi : i ∈ θ) (γ : V)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) {G : Set V}
    (hG : IsExternalForcingFilter
      ((forcingCodeP (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ)
      ((forcingCodeR (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) G) :
    (
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    let G' := forcingProjectionGeneric ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s γ) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingCodeπ z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodeπ z) ‘ ⟨i, θ⟩ₖ) G )
  inheritedSupport {α f : V} [IsOrdinal α] [IsFunction f]
      (hf : domain f = θ) (hα : α ⊆ θ) (hzero : (∅ : V) ∈ α) :
    (∃ k, IsThreadSupport (woodinSourceIndex α)
      (woodinSeedSections θ (forcingCodeE s) (forcingCodet s))
      ((woodinInsertSeed θ f ∅) ↾ (woodinSourceIndex α)) k) ↔
    ∃ k, IsThreadSupport α (forcingCodeE s) (f ↾ α) k

theorem woodinSourceCodeCompatibility {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (K : V) : WoodinSourceCodeCompatibility θ s K where
  code := woodinSourceCode_valid (θ := θ) (s := s) hs
  stage := woodinSourceCode_stage (θ := θ) (s := s) (K := K)
  seed := woodinSourceCode_seed (θ := θ) (s := s) (K := K)
  projection := woodinSourceCode_projection (θ := θ) (s := s)
  sectionMap := woodinSourceCode_section (θ := θ) (s := s)
  replacement := woodinSourceCode_lift (θ := θ) (s := s)
  cardinal := woodinSourceCardinals_stage (θ := θ) (K := K)
  quotientClosure := woodinSourceCode_quotient_iff (θ := θ) (s := s)
  rawInverse := woodinSourceCode_inverse_isomorphism (θ := θ) (s := s) hs
  direct := woodinSourceCode_direct_isomorphism (θ := θ) (s := s) hs
  rawTop := woodinSourceCode_inverse_top (θ := θ) (s := s) hs
  rawProjection := woodinSourceCode_inverse_projection (θ := θ) (s := s) hs
  directProjection := woodinSourceCode_direct_projection (θ := θ) (s := s) hs
  rawSection := woodinSourceCode_inverse_section (θ := θ) (s := s) hs
  directSection := woodinSourceCode_direct_section (θ := θ) (s := s) hs
  rawReplacement := woodinSourceCode_inverse_replacement (θ := θ) (s := s) hs
  directReplacement := woodinSourceCode_direct_replacement (θ := θ) (s := s) hs
  completed := woodinSourceCode_completed_inverse_isomorphism (θ := θ) (s := s) hs
  completedProjection := woodinSourceCode_completed_inverse_projection (θ := θ) (s := s) hs
  completedSection := woodinSourceCode_completed_inverse_section_of_valid (θ := θ) (s := s) hs
  completedReplacement := woodinSourceCode_completed_inverse_replacement_of_valid (θ := θ) (s := s) hs
  seedProjection := woodinSourceCode_limit_seed_projection (θ := θ) (s := s)
  seedSection := woodinSourceCode_limit_seed_section (θ := θ) (s := s)
  seedReplacement := woodinSourceCode_limit_seed_replacement (θ := θ) (s := s)
  completedSeedProjection := woodinSourceCode_completed_seed_projection (θ := θ) (s := s)
  completedSeedSection := woodinSourceCode_completed_seed_section (θ := θ) (s := s) hs
  completedSeedReplacement := woodinSourceCode_completed_seed_replacement (θ := θ) (s := s)
  rawTopValue := woodinSourceCode_inverse_top_value (θ := θ) (s := s) hs
  rawCutoff := woodinSourceCode_inverse_cutoff (θ := θ) (s := s) hs
  rawTransport := (woodinSourceCode_inverse_isomorphism hs).canonicalTransport
  directTransport hzero := (woodinSourceCode_direct_isomorphism hs hzero).canonicalTransport
  completedTransport hzero γ := (woodinSourceCode_completed_inverse_isomorphism hs hzero γ).canonicalTransport
  rawGenericProjection := woodinSourceCode_inverse_generic_projection (θ := θ) (s := s) hs
  directGenericProjection := woodinSourceCode_direct_generic_projection (θ := θ) (s := s) hs
  completedGenericProjection := woodinSourceCode_completed_generic_projection (θ := θ) (s := s) hs
  inheritedSupport := by
    intros
    apply woodinSeed_inherited_support_iff <;> first | assumption | exact hs.system.tops.secTop
theorem woodinSourceCode_actual_prefix_compatibility {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ⊆ δ) :
    WoodinSourceCodeCompatibility θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) := by
  have hx := woodinIterationExit hδ hAC
  exact woodinSourceCodeCompatibility
    (woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)).code _

theorem woodinSourceCode_actual_full_compatibility {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    let _ := hδ.inaccessible.1
    WoodinSourceCodeCompatibility (succ δ) (kpair.π₁ (woodinIterationRec δ))
      (kpair.π₂ (woodinIterationRec δ)) := by
  let := hδ.inaccessible.1
  exact woodinSourceCodeCompatibility (woodinIteration_endpoint_valid hδ hAC).1.code _
end ZFVP

