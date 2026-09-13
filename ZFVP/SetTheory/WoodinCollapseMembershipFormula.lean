import ZFVP.SetTheory.WoodinCollapseFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinCollapseMembershipFormula : SetTheorySemisentence 3 :=
  “p κ δ. ∃ H, (∀ x ∈ H, !sigmaOneRankLtFormula x δ) ∧ !sigmaOneWoodinConditionFormula p κ δ H”

theorem sigmaOneWoodinCollapseMembershipFormula_sigmaOne :
    IsSigmaFormula 1 sigmaOneWoodinCollapseMembershipFormula :=
  .exs (.and (.boundedAll (.bvar 0) (sigmaOneRankLtFormula_sigmaOne.subst _))
    (sigmaOneWoodinConditionFormula_sigmaOne.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sigmaOneWoodinConditionFormula_mono {p κ δ H K : V} [IsOrdinal δ]
    (hHK : H ⊆ K) : sigmaOneWoodinConditionFormula.Evalb ![p,κ,δ,H] →
      sigmaOneWoodinConditionFormula.Evalb ![p,κ,δ,K] := by
  have hrow : ∀ z, sigmaOneWoodinRowFormula.Evalb ![z,κ,δ,H] →
      sigmaOneWoodinRowFormula.Evalb ![z,κ,δ,K] := by
    intro z hz
    obtain ⟨a,ha,η,hη,x,hx,he,hr⟩ := (eval_sigmaOneWoodinRowFormula z κ δ H).mp hz
    exact (eval_sigmaOneWoodinRowFormula z κ δ K).mpr ⟨a,ha,η,hη,x,hHK x hx,he,hr⟩
  have he (L : V) : sigmaOneWoodinConditionFormula.Evalb ![p,κ,δ,L] ↔
      (∃ D, boundedFunctionDomainFormula.Evalb ![p,D] ∧
        ∃ α ∈ κ, ∃ g, boundedInjectionFormula.Evalb ![g,D,α]) ∧
      ∀ z ∈ p, sigmaOneWoodinRowFormula.Evalb ![z,κ,δ,L] := by
    simp [sigmaOneWoodinConditionFormula]
  rw [he H,he K]
  exact fun h ↦ ⟨h.1,fun z hz ↦ hrow z (h.2 z hz)⟩

theorem eval_sigmaOneWoodinCollapseMembershipFormula (p κ δ : V) [IsOrdinal δ] :
    sigmaOneWoodinCollapseMembershipFormula.Evalb ![p,κ,δ] ↔ p ∈ woodinCollapse κ δ := by
  have he : sigmaOneWoodinCollapseMembershipFormula.Evalb ![p,κ,δ] ↔
      ∃ H : V, (∀ x ∈ H, rank x ∈ δ) ∧ sigmaOneWoodinConditionFormula.Evalb ![p,κ,δ,H] := by
    simp [sigmaOneWoodinCollapseMembershipFormula,eval_sigmaOneRankLtFormula]
  rw [he]
  constructor
  · rintro ⟨H,hH,hp⟩
    exact (eval_sigmaOneWoodinConditionFormula p κ δ).mp
      (sigmaOneWoodinConditionFormula_mono (fun x hx ↦ (mem_hierarchy_iff_rank_mem x δ).mpr (hH x hx)) hp)
  · intro hp
    exact ⟨hierarchy δ,fun x hx ↦ (mem_hierarchy_iff_rank_mem x δ).mp hx,
      (eval_sigmaOneWoodinConditionFormula p κ δ).mpr hp⟩

end ZFVP
