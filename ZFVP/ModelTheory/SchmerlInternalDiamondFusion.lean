import ZFVP.ModelTheory.SchmerlInternalDiamondClubSteps
import ZFVP.SetTheory.InfiniteDependentChoice

/-! Fusion through the ground model's full internal omega. The union
condition decides its entire domain and forces that domain into the club. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem exists_diamondFusionSequence [Countable V] {κ τ σ base p : V}
    (hAC : InternalChoice V) (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hcount : ∀ α ∈ κ, IsInternallyCountable α)
    (hσ : IsForcingName (diamondConditions κ) σ)
    (hbase : ForcesClubName (diamondConditions κ) (diamondOrder κ) ∅ κ σ base)
    (hp : p ∈ diamondConditions κ) (hbp : base ⊆ p) :
    ∃ f, IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f ∧
      f ‘ 0 = p ∧ ∀ n ∈ (ω : V), DiamondFusionStep κ τ σ (f ‘ n) (f ‘ (succ n)) := by
  let C := {q ∈ diamondConditions κ ; base ⊆ q}
  let E := {z ∈ C ×ˢ C ; DiamondFusionStep κ τ σ (kpair.π₁ z) (kpair.π₂ z)}
  have hE (q r : V) : ⟨q, r⟩ₖ ∈ E ↔ q ∈ C ∧ r ∈ C ∧ DiamondFusionStep κ τ σ q r := by
    simp only [E, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
  have hserial : ∀ q ∈ C, ∃ r ∈ C, ⟨q, r⟩ₖ ∈ E := by
    intro q hq
    obtain ⟨r, hr, hqr⟩ := exists_diamondFusionStep hκ hω hcount
      (dependentChoiceAt_of_internalChoice hAC _) hσ hbase
      (mem_sep_iff.mp hq).1 (mem_sep_iff.mp hq).2
    have hrC : r ∈ C := mem_sep_iff.mpr ⟨hr, subset_trans (mem_sep_iff.mp hq).2 hqr.1⟩
    exact ⟨r, hrC, (hE q r).mpr ⟨hq, hrC, hqr⟩⟩
  obtain ⟨f, hf, hf0, hsteps⟩ := pointedDependentChoice_of_internalChoice hAC C E p
    (mem_sep_iff.mpr ⟨hp, hbp⟩) hserial
  have hfP : f ∈ (diamondConditions κ) ^ (ω : V) :=
    mem_function_of_mem_function_of_subset hf sep_subset
  have hs (n : V) (hn : n ∈ (ω : V)) : DiamondFusionStep κ τ σ (f ‘ n) (f ‘ (succ n)) :=
    ((hE _ _).mp (hsteps n hn)).2.2
  have hinc := natural_increasing_subset (fun n ↦ f ‘ n) (by definability) (fun n hn ↦ (hs n hn).1)
  exact ⟨f, ⟨hfP, fun i hi j hj ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨function_value_mem hfP hi, function_value_mem hfP (IsOrdinal.toIsTransitive.mem_trans hj hi),
      hinc i hi j hj⟩⟩, hf0, hs⟩

theorem diamondFusion_union_contains {κ f : V}
    (hf : IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f)
    {n : V} (hn : n ∈ (ω : V)) : (f ‘ n) ⊆ ⋃ˢ range f := by
  let : IsFunction f := IsFunction.of_mem hf.1
  intro z hz
  exact mem_sUnion_iff.mpr ⟨f ‘ n, mem_range_of_kpair_mem
    (kpair_value_mem ((domain_eq_of_mem_function hf.1).symm ▸ hn)), hz⟩

theorem diamondFusion_domain_witness {κ f x : V}
    (hf : IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f)
    (hx : x ∈ domain (⋃ˢ range f)) : ∃ n ∈ (ω : V), x ∈ domain (f ‘ n) := by
  let : IsFunction f := IsFunction.of_mem hf.1
  obtain ⟨p, hp, hxp⟩ := (mem_domain_sUnion_iff _ _).mp hx
  obtain ⟨n, hnp⟩ := mem_range_iff.mp hp
  exact ⟨n, domain_eq_of_mem_function hf.1 ▸ mem_domain_of_kpair_mem hnp,
    (value_eq_of_kpair_mem hnp).symm ▸ hxp⟩

theorem diamondFusion_limit_decides {κ τ σ f : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hf : IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f)
    (hs : ∀ n ∈ (ω : V), DiamondFusionStep κ τ σ (f ‘ n) (f ‘ (succ n))) :
    DecidesMembershipOn (diamondConditions κ) (diamondOrder κ) ∅ τ
      (⋃ˢ range f) (domain (⋃ˢ range f)) := by
  have hq := diamond_chain_union hκ hω hf
  intro x hx
  obtain ⟨n, hn, hxn⟩ := diamondFusion_domain_witness hf hx
  exact decidesMembershipOn_mono (diamond_poset κ).1 (hs n hn).2.1 hq
    ((pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hq, function_value_mem hf.1 (ω_succ_closed hn), diamondFusion_union_contains hf (ω_succ_closed hn)⟩) x hxn

/-- The limit belongs to the named club in every generic containing the
union condition. This uses club closure in the actual forcing quotient. -/
theorem diamondFusion_limit_forces_club [Countable V] {κ τ σ base f : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hσ : IsForcingName (diamondConditions κ) σ)
    (hbase : ForcesClubName (diamondConditions κ) (diamondOrder κ) ∅ κ σ base)
    (hf : IsForcingDescending (diamondConditions κ) (diamondOrder κ) (ω : V) f)
    (hbf : base ⊆ (f ‘ 0))
    (hs : ∀ n ∈ (ω : V), DiamondFusionStep κ τ σ (f ‘ n) (f ‘ (succ n))) :
    ⋃ˢ range f ∈ atomicMembership (diamondConditions κ) (diamondOrder κ)
      (checkName ∅ (domain (⋃ˢ range f))) σ := by
  let : IsOrdinal κ := hκ.1.1
  let q := ⋃ˢ range f
  let α := domain q
  have hq := diamond_chain_union hκ hω hf
  have hα : α ∈ κ := ((mem_diamondConditions κ q).mp hq).1
  have hR := (diamond_poset κ).1
  have hz : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω
  have htop := diamond_top hz
  have hbP := (forcingFormula_regular hR clubInFormula _).1 base hbase
  have hbq : base ⊆ q := subset_trans hbf (diamondFusion_union_contains hf (by simp))
  have hqb : ⟨q, base⟩ₖ ∈ diamondOrder κ := (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hbP, hbq⟩
  apply atomicMembership_of_all_generics hR htop hq
    ⟨checkName ∅ α, checkName_isName htop.1 α⟩ ⟨σ, hσ⟩
  intro G hG hqG
  let F : ForcingContext V := ⟨diamondConditions κ, diamondOrder κ, ∅, G, hR, htop, hG⟩
  have hbG := hG.1.2.2.1 q hqG base hbP hqb
  have hC := (F.clubName_truth ⟨σ, hσ⟩ κ).mpr ⟨base, hbG, hbase⟩
  have hbound (n : V) (hn : n ∈ (ω : V)) :
      ∃ β ∈ κ, domain (f ‘ n) ∈ β ∧ β ∈ α ∧ F.check β ∈ F.ofName ⟨σ, hσ⟩ := by
    obtain ⟨β, hβ, hnβ, hβn, hnforce⟩ := (hs n hn).2.2
    have hsub := diamondFusion_union_contains hf (ω_succ_closed hn)
    have hβq : β ∈ α := by
      obtain ⟨x, hβx⟩ := mem_domain_iff.mp hβn
      exact mem_domain_of_kpair_mem (hsub _ hβx)
    have hqβ := atomicMembership_mono hR hnforce hq
      ((pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hq, function_value_mem hf.1 (ω_succ_closed hn), hsub⟩)
    exact ⟨β, hβ, hnβ, hβq, (show F.check β ∈ F.ofName ⟨σ, hσ⟩ from ⟨q, hqG, hqβ⟩)⟩
  apply hC.1.2 (F.check α) ((F.check_mem_iff α κ).mpr hα)
  · intro he
    obtain ⟨β, _, _, hβα, _⟩ := hbound 0 (by simp)
    have hm := (F.check_mem_iff β α).mpr hβα
    exact not_mem_empty (he ▸ hm)
  · intro x hx
    obtain ⟨ξ, hξ, rfl⟩ := (F.mem_check_iff α x).mp hx
    obtain ⟨n, hn, hξn⟩ := diamondFusion_domain_witness hf hξ
    obtain ⟨β, hβ, hnβ, hβα, hβC⟩ := hbound n hn
    let : IsOrdinal β := IsOrdinal.of_mem hβ
    exact ⟨F.check β, hβC, (F.check_mem_iff β α).mpr hβα,
      (F.check_mem_iff ξ β).mpr (IsOrdinal.toIsTransitive.mem_trans hξn hnβ)⟩

end ZFVP.Schmerl
