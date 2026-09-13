import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.ModelTheory.ClassForcingQuotientTruth
import ZFVP.SetTheory.ElementaryMap

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLowRankForcingName (P δ τ : V) : Prop := τ ∈ hierarchy δ ∧ IsForcingName P τ

instance lowRankForcingName_definable (P δ : V) : ℒₛₑₜ-predicate[V] (IsLowRankForcingName P δ) := by
  unfold IsLowRankForcingName
  definability

theorem lowRankForcingName_subname {P δ τ u p : V} [IsOrdinal δ]
    (hτ : IsLowRankForcingName P δ τ) (hu : ⟨u, p⟩ₖ ∈ τ) : IsLowRankForcingName P δ u := by
  let := hierarchy_transitive δ
  exact ⟨(kpair_components_mem_transitive ((hierarchy_transitive δ).mem_trans hu hτ.1)).1,
    forcingName_subname hτ.2 hu⟩

namespace ForcingContext
variable (A : ForcingContext V) {δ : V}

abbrev RankNameModel (δ : V) := ClassForcingQuotient A.P A.R A.G A.order A.generic.1
  (IsLowRankForcingName A.P δ) (fun _ h ↦ h.2)

def rankNameEquiv (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) :
    A.RankNameModel δ ≃ SetDomain (hierarchy (A.check δ)) where
  toFun x := ⟨x.val, by
    obtain ⟨τ, hτ, he⟩ := x.property
    exact (A.mem_checked_hierarchy_iff_low_name hδ hP x.val).mpr ⟨⟨τ, hτ.2⟩, hτ.1, he⟩⟩
  invFun x := ⟨x.val, by
    obtain ⟨τ, hτ, he⟩ := (A.mem_checked_hierarchy_iff_low_name hδ hP x.val).mp x.property
    exact ⟨τ.val, ⟨hτ, τ.property⟩, he⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rankNameElementaryMap (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) :
    ElementaryMap (A.RankNameModel δ) (SetDomain (hierarchy (A.check δ))) :=
  ElementaryMap.ofMembershipIso (A.rankNameEquiv hδ hP) (fun _ _ ↦ Iff.rfl)

theorem rankName_formula_truth (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName A.P)
    (hv : ∀ i, (v i).val ∈ hierarchy δ) :
    φ.Evalb (show Fin n → SetDomain (hierarchy (A.check δ)) from fun i ↦ (⟨A.ofName (v i),
      (A.mem_checked_hierarchy_iff_low_name hδ hP _).mpr ⟨v i, hv i, rfl⟩⟩ :
        SetDomain (hierarchy (A.check δ)))) ↔
      GenericMeets A.G (classForcingFormula A.P A.R (IsLowRankForcingName A.P δ)
        (by definability) φ (standardTuple (fun i ↦ (v i).val))) := by
  let w : Fin n → {τ : V // IsLowRankForcingName A.P δ τ} := fun i ↦ ⟨(v i).val, hv i, (v i).property⟩
  let a := ClassForcingQuotient.assignment A.P A.R A.G A.order A.generic.1
    (IsLowRankForcingName A.P δ) (fun _ h ↦ h.2) w
  let j := A.rankNameElementaryMap hδ hP
  have he := j.elementary φ a Empty.elim
  have hz : j ∘ (Empty.elim : Empty → A.RankNameModel δ) = Empty.elim := by
    funext i
    exact Empty.elim i
  rw [hz] at he
  exact he.symm.trans (ClassForcingQuotient.formula_truth A.P A.R A.G A.order A.generic
    (IsLowRankForcingName A.P δ) (by definability) (fun _ h ↦ h.2) φ w)

end ForcingContext
end ZFVP
