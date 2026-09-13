import ZFVP.ModelTheory.SchmerlInternalDiamondExtensions
import ZFVP.ModelTheory.SchmerlInternalDiamondDecisions
import ZFVP.SetTheory.ClubDictionary

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

def ForcesClubName (P R one κ σ p : V) : Prop :=
  p ∈ forcingFormula P R clubInFormula (standardTuple ![σ, checkName one κ])

instance forcesClubName_definable (P R one κ σ : V) :
    ℒₛₑₜ-predicate[V] (ForcesClubName P R one κ σ) := by
  unfold ForcesClubName
  simp only [standardTuple]
  definability

def DiamondFusionStep (κ τ σ p q : V) : Prop :=
  p ⊆ q ∧ DecidesMembershipOn (diamondConditions κ) (diamondOrder κ) ∅ τ q (domain p) ∧
    ∃ β ∈ κ, domain p ∈ β ∧ β ∈ domain q ∧
      q ∈ atomicMembership (diamondConditions κ) (diamondOrder κ) (checkName ∅ β) σ

instance diamondFusionStep_definable (κ τ σ : V) :
    ℒₛₑₜ-relation[V] (DiamondFusionStep κ τ σ) := by
  unfold DiamondFusionStep
  definability

end Schmerl

namespace ForcingContext

open Schmerl

theorem clubName_truth (F : ForcingContext V) (σ : ForcingName F.P) (κ : V) :
    IsClubIn (F.ofName σ) (F.check κ) ↔
      ∃ p ∈ F.G, ForcesClubName F.P F.R F.one κ σ.val p := by
  let ν : ForcingName F.P := ⟨checkName F.one κ, checkName_isName F.top.1 κ⟩
  constructor
  · intro h
    apply (F.formula_truth clubInFormula ![σ, ν]).mp
    exact (Defined.eval_iff _).mpr h
  · intro h
    exact (Defined.eval_iff _).mp ((F.formula_truth clubInFormula ![σ, ν]).mpr h)

end ForcingContext

namespace Schmerl

variable [Countable V]

/-- A single internal fusion step decides the earlier initial segment and
places a forced club point strictly between the old and new lengths. -/
theorem exists_diamondFusionStep {κ τ σ base p : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hcount : ∀ α ∈ κ, IsInternallyCountable α)
    (hDC : InternalDependentChoiceAt (ω : V))
    (hσ : IsForcingName (diamondConditions κ) σ)
    (hbase : ForcesClubName (diamondConditions κ) (diamondOrder κ) ∅ κ σ base)
    (hp : p ∈ diamondConditions κ) (hbp : base ⊆ p) :
    ∃ q ∈ diamondConditions κ, DiamondFusionStep κ τ σ p q := by
  let : IsOrdinal κ := hκ.1.1
  have hz : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω
  have hR := (diamond_poset κ).1
  have htop := diamond_top hz
  have hbP := (forcingFormula_regular hR clubInFormula _).1 base hbase
  have hpb : ⟨p, base⟩ₖ ∈ diamondOrder κ :=
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hbP, hbp⟩
  have hpdom := ((mem_diamondConditions κ p).mp hp).1
  obtain ⟨q, hqD, hqp⟩ := (decidesMembershipOn_dense hR htop hDC
    (diamond_closedAt_omega hκ hω) (hcount _ hpdom) (τ := τ)).2 p hp
  have hq := (mem_sep_iff.mp hqD).1
  have hqdec := (mem_sep_iff.mp hqD).2
  have hqb := hR.2.2 q hq p hp base hbP hqp hpb
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let F : ForcingContext V := ⟨diamondConditions κ, diamondOrder κ, ∅, G, hR, htop, hG⟩
  have hbG := hG.1.2.2.1 q hqG base hbP hqb
  have hclub := (F.clubName_truth ⟨σ, hσ⟩ κ).mpr ⟨base, hbG, hbase⟩
  obtain ⟨β', hβC, hpβ⟩ := hclub.2.2 (F.check (domain p)) ((F.check_mem_iff _ _).mpr hpdom)
  obtain ⟨β, hβ, rfl⟩ := (F.mem_check_iff κ β').mp (hclub.2.1 β' hβC)
  have hpβ' := (F.check_mem_iff (domain p) β).mp hpβ
  have hmem : ∃ r ∈ G, r ∈ atomicMembership (diamondConditions κ) (diamondOrder κ)
      (checkName ∅ β) σ := hβC
  obtain ⟨r, hrG, hrβ⟩ := hmem
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  have hs := hG.1.1 s hsG
  obtain ⟨t, htD, hts⟩ := (diamond_domain_dense hκ hω hβ).2 s hs
  have ht := (mem_sep_iff.mp htD).1
  have htq := hR.2.2 t ht s hs q hq hts hsq
  have htp := hR.2.2 t ht q hq p hp htq hqp
  have htr := hR.2.2 t ht s hs r (hG.1.1 r hrG) hts hsr
  exact ⟨t, ht, ((pair_mem_reverseInclusionOrder _ _ _).mp htp).2.2,
    decidesMembershipOn_mono hR hqdec ht htq, β, hβ, hpβ', (mem_sep_iff.mp htD).2,
    atomicMembership_mono hR hrβ ht htr⟩

end Schmerl
end ZFVP
