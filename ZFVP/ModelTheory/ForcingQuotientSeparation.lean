import ZFVP.ModelTheory.ForcingQuotientNames
import ZFVP.SetTheory.ForcingSelectedName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSelected {P : V} (R : V) (τ : ForcingName P)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : ForcingName P :=
  ⟨forcingSelectedName P R τ.val F hF, forcingSelectedName_isName τ.property F hF⟩

theorem forcingQuotient_selectedName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hd : ∀ ν, IsForcingName P ν → IsForcingDownwardClosed P R (F ν))
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingSelected R τ F hF) ↔
      ∃ ν : ForcingName P, ∃ s ∈ G, ⟨ν.val, s⟩ₖ ∈ τ.val ∧
        x = forcingQuotientMk P R G hR hG.1 ν ∧ GenericMeets G (F ν.val) := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  rw [forcingQuotientMk_mem_subname_iff P R G hR hG]
  constructor
  · rintro ⟨ν, q, hqG, hνq, he⟩
    obtain ⟨_, s, hs, hqs, hqF⟩ := (mem_forcingSelectedName_iff P R τ.val F hF _ _).mp hνq
    exact ⟨ν, s, hG.1.2.2.1 q hqG s (forcingOrder_right_mem hR hqs) hqs,
      hs, he, q, hqG, hqF⟩
  · rintro ⟨ν, s, hsG, hs, he, p, hpG, hpF⟩
    obtain ⟨q, hqG, hqs, hqp⟩ := hG.1.2.2.2 s hsG p hpG
    exact ⟨ν, q, hqG, (mem_forcingSelectedName_iff P R τ.val F hF _ _).mpr
      ⟨hG.1.1 q hqG, s, hs, hqs, hd ν.val ν.property p hpF q (hG.1.1 q hqG) hqp⟩, he⟩

theorem forcingQuotient_separationName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → ForcingName P)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingSelected R τ
      (fun ν ↦ forcingFormula P R φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν))
      (by definability)) ↔ x ∈ forcingQuotientMk P R G hR hG.1 τ ∧
        φ.Evalb (x :> forcingQuotientAssignment P R G hR hG.1 v) := by
  unfold IsExternalForcingGeneric at hG
  rw [forcingQuotient_selectedName P R G hR hG τ _ _
    (fun ν _ ↦ (forcingFormula_regular hR φ _).2.1)]
  have htruth (ν : ForcingName P) :
      GenericMeets G (forcingFormula P R φ
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν.val)) ↔
      φ.Evalb (forcingQuotientMk P R G hR hG.1 ν :> forcingQuotientAssignment P R G hR hG.1 v) := by
    simpa only [forcingNameTuple_cons, forcingQuotientAssignment_cons] using
      (forcingFormula_quotient_truth P R G hR hG φ (ν :> v)).symm
  constructor
  · rintro ⟨ν, s, hsG, hs, rfl, hF⟩
    exact ⟨(forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr ⟨ν, s, hsG, hs, rfl⟩,
      (htruth ν).mp hF⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
    obtain ⟨ν, s, hsG, hs, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    refine ⟨ν, s, hsG, hs, he, (htruth ν).mpr ?_⟩
    rwa [he] at hφ

theorem forcingQuotient_separation (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingQuotient P R G hR hG.1) (a : ForcingQuotient P R G hR hG.1) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ x, x ∈ b ↔ x ∈ a ∧ φ.Evalb (x :> v) := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 a
  choose w hw using fun i ↦ forcingQuotientMk_surjective P R G hR hG.1 (v i)
  have he : forcingQuotientAssignment P R G hR hG.1 w = v := funext hw
  refine ⟨forcingQuotientMk P R G hR hG.1 (forcingSelected R τ
    (fun ν ↦ forcingFormula P R φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (w i).val)) ν))
    (by definability)), ?_⟩
  simpa only [he] using forcingQuotient_separationName P R G hR hG τ φ w

end ZFVP
