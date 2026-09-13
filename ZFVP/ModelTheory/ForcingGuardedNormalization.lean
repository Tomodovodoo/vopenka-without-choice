import ZFVP.ModelTheory.ForcingRestrictedName
import ZFVP.ModelTheory.ForcingLeastRankNameBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingRestrictedName_forces_empty_of_incompatible {P R p q τ : V}
    (hR : IsForcingPreorder P R) (hq : q ∈ P)
    (hinc : ¬ ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ⟨r, p⟩ₖ ∈ R) :
    q ∈ atomicEquality P R (forcingRestrictedName P R p τ) ∅ := by
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hq, ?_, ?_⟩
  · intro σ s hs r hr hrq hrs
    obtain ⟨hsP, hsp, _⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hs
    exact False.elim (hinc ⟨r, hr, hrq,
      hR.2.2 r hr s hsP p (forcingOrder_right_mem hR hsp) hrs hsp⟩)
  · intro σ s hs
    exact False.elim (not_mem_empty hs)

/-- Local membership becomes global membership when the default empty name is
globally a member of the target. -/
theorem forcingRestrictedName_forces_member {P R one p τ Q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (hτ : p ∈ atomicMembership P R τ Q)
    (h0 : one ∈ atomicMembership P R ∅ Q) :
    one ∈ atomicMembership P R (forcingRestrictedName P R p τ) Q := by
  apply atomicMembership_dense hR ht.1
  intro q hq _
  by_cases hc : ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ⟨r, p⟩ₖ ∈ R
  · obtain ⟨r, hr, hrq, hrp⟩ := hc
    have he := atomicEquality_mono hR (forcingRestrictedName_forces hR hp τ) hr hrp
    exact ⟨r, ((atomicEquality_membership_iff hR he Q).1).mpr
      (atomicMembership_mono hR hτ hr hrp), hrq⟩
  · have he := forcingRestrictedName_forces_empty_of_incompatible hR hq hc (τ := τ)
    exact ⟨q, ((atomicEquality_membership_iff hR he Q).1).mpr
      (atomicMembership_mono hR h0 hq (ht.2 q hq)), hR.2.1 q hq⟩

/-- The guard followed by the manuscript's global minimum-rank normalization. -/
noncomputable def forcingGuardedNormalization (P R one p τ : V) : V :=
  forcingLeastRankName P R one (forcingRestrictedName P R p τ)

theorem forcingGuardedNormalization_isName {P R one p τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ) :
    IsForcingName P (forcingGuardedNormalization P R one p τ) :=
  forcingLeastRankName_isName hR ht.1 (forcingRestrictedName_isName (R := R) (p := p) hτ)

theorem forcingGuardedNormalization_forces_equal {P R one p τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hτ : IsForcingName P τ) :
    p ∈ atomicEquality P R (forcingGuardedNormalization P R one p τ) τ := by
  have he := atomicEquality_mono hR
    (forcingLeastRankName_forced_equal hR ht.1 (forcingRestrictedName_isName (R := R) (p := p) hτ)) hp (ht.2 p hp)
  rw [atomicEquality_symm] at he
  exact atomicEquality_trans hR _ _ _ p he (forcingRestrictedName_forces hR hp τ)

theorem forcingGuardedNormalization_forces_member {P R one p τ Q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (hname : IsForcingName P τ) (hτ : p ∈ atomicMembership P R τ Q)
    (h0 : one ∈ atomicMembership P R ∅ Q) :
    one ∈ atomicMembership P R (forcingGuardedNormalization P R one p τ) Q := by
  have he := forcingLeastRankName_forced_equal hR ht.1 (forcingRestrictedName_isName (R := R) (p := p) hname)
  exact ((atomicEquality_membership_iff hR he Q).1).mp
    (forcingRestrictedName_forces_member hR ht hp hτ h0)

theorem forcingGuardedNormalization_normalized {P R one p τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ) :
    forcingLeastRankName P R one (forcingGuardedNormalization P R one p τ) =
      forcingGuardedNormalization P R one p τ :=
  forcingLeastRankName_idempotent hR ht.1 (forcingRestrictedName_isName (R := R) (p := p) hτ)

theorem forcingGuardedNormalization_empty_of_forced {P R one p τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (he : p ∈ atomicEquality P R τ ∅) :
    forcingGuardedNormalization P R one p τ = ∅ := by
  unfold forcingGuardedNormalization
  rw [forcingRestrictedName_empty_of_forced hR he, forcingLeastRankName_empty hR ht.1]

theorem forcingRestrictedName_mem_hierarchy {P R p τ δ : V} [IsOrdinal δ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hτ : τ ∈ hierarchy δ) :
    forcingRestrictedName P R p τ ∈ hierarchy δ := by
  have hd : domain τ ∈ hierarchy δ := subset_mem_hierarchy_limit hδ
    (sUnion_mem_hierarchy_limit hδ (sUnion_mem_hierarchy_limit hδ hτ))
    (fun _ hz ↦ (mem_sep_iff.mp hz).1)
  exact subset_mem_hierarchy_limit hδ (prod_mem_hierarchy_limit hδ hd hP) sep_subset

theorem forcingGuardedNormalization_mem_hierarchy {P R one p τ δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hτ : IsForcingName P τ) (hτδ : τ ∈ hierarchy δ) :
    forcingGuardedNormalization P R one p τ ∈ hierarchy δ := by
  exact forcingLeastRankName_mem_hierarchy_of_equiv hR ht.1
    (forcingRestrictedName_isName hτ) (forcingRestrictedName_isName hτ)
    (by rw [atomicEquality_refl hR]; exact ht.1) (forcingRestrictedName_mem_hierarchy hδ hP hτδ)

theorem ForcingContext.restrictedName_value_of_not_mem (A : ForcingContext V) {p : V}
    (hp : p ∈ A.P) (hnot : p ∉ A.G) (τ : ForcingName A.P) :
    A.ofName ⟨forcingRestrictedName A.P A.R p τ.val, forcingRestrictedName_isName τ.property⟩ = ∅ := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨σ, r, hrG, hσr, _⟩
    have hrp := ((pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hσr).2.1
    exact False.elim (hnot (A.generic.1.2.2.1 r hrG p hp hrp))
  · intro hx
    exact False.elim (not_mem_empty hx)

end ZFVP
