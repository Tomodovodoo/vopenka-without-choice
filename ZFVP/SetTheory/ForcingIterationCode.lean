import ZFVP.SetTheory.ForcingIterationUnion
import ZFVP.SetTheory.ForcingIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingIterationCode (P R π E L t : V) : V :=
  ⟨P, ⟨R, ⟨π, ⟨E, ⟨L, t⟩ₖ⟩ₖ⟩ₖ⟩ₖ⟩ₖ

noncomputable def forcingCodeP (s : V) : V := kpair.π₁ (s)

instance forcingCodeP_definable : ℒₛₑₜ-function₁[V] forcingCodeP := by
  unfold forcingCodeP
  definability

@[simp] theorem forcingCodeP_code (P R π E L t : V) :
    forcingCodeP (forcingIterationCode P R π E L t) = P := by
  simp [forcingCodeP, forcingIterationCode]

noncomputable def forcingCodeR (s : V) : V := kpair.π₁ (kpair.π₂ (s))

instance forcingCodeR_definable : ℒₛₑₜ-function₁[V] forcingCodeR := by
  unfold forcingCodeR
  definability

@[simp] theorem forcingCodeR_code (P R π E L t : V) :
    forcingCodeR (forcingIterationCode P R π E L t) = R := by
  simp [forcingCodeR, forcingIterationCode]

noncomputable def forcingCodeπ (s : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ (s)))

instance forcingCodeπ_definable : ℒₛₑₜ-function₁[V] forcingCodeπ := by
  unfold forcingCodeπ
  definability

@[simp] theorem forcingCodeπ_code (P R π E L t : V) :
    forcingCodeπ (forcingIterationCode P R π E L t) = π := by
  simp [forcingCodeπ, forcingIterationCode]

noncomputable def forcingCodeE (s : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ (s))))

instance forcingCodeE_definable : ℒₛₑₜ-function₁[V] forcingCodeE := by
  unfold forcingCodeE
  definability

@[simp] theorem forcingCodeE_code (P R π E L t : V) :
    forcingCodeE (forcingIterationCode P R π E L t) = E := by
  simp [forcingCodeE, forcingIterationCode]

noncomputable def forcingCodeL (s : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (s)))))

instance forcingCodeL_definable : ℒₛₑₜ-function₁[V] forcingCodeL := by
  unfold forcingCodeL
  definability

@[simp] theorem forcingCodeL_code (P R π E L t : V) :
    forcingCodeL (forcingIterationCode P R π E L t) = L := by
  simp [forcingCodeL, forcingIterationCode]

noncomputable def forcingCodet (s : V) : V := kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (kpair.π₂ (s)))))

instance forcingCodet_definable : ℒₛₑₜ-function₁[V] forcingCodet := by
  unfold forcingCodet
  definability

@[simp] theorem forcingCodet_code (P R π E L t : V) :
    forcingCodet (forcingIterationCode P R π E L t) = t := by
  simp [forcingCodet, forcingIterationCode]

structure IsForcingIterationCode (θ s : V) : Prop where
  system : IsForcingIterationSystem θ (forcingCodeP s) (forcingCodeR s)
    (forcingCodeπ s) (forcingCodeE s) (forcingCodeL s) (forcingCodet s)
  tableP : IsIterationTable (θ) (forcingCodeP s)
  tableR : IsIterationTable (θ) (forcingCodeR s)
  tableπ : IsIterationTable (θ ×ˢ θ) (forcingCodeπ s)
  tableE : IsIterationTable (θ ×ˢ θ) (forcingCodeE s)
  tableL : IsIterationTable (θ ×ˢ θ) (forcingCodeL s)
  tablet : IsIterationTable (θ) (forcingCodet s)

noncomputable def forcingIterationCodeNext (θ s Q T ρ F M u : V) : V :=
  forcingIterationCode (forcingFamilyNext θ (forcingCodeP s) Q)
    (forcingFamilyNext θ (forcingCodeR s) T)
    (forcingMatrixNext θ (forcingCodeπ s) ρ (identity Q))
    (forcingMatrixNext θ (forcingCodeE s) F (identity Q))
    (forcingMatrixNext θ (forcingCodeL s) M (forcingIdentityLift Q))
    (forcingFamilyNext θ (forcingCodet s) u)

theorem IsForcingIterationCode.extend {θ s Q T ρ F M u : V}
    (h : IsForcingIterationCode θ s)
    (c : IsForcingIterationColumn θ (forcingCodeP s) (forcingCodeR s)
      (forcingCodeπ s) (forcingCodeE s) (forcingCodeL s) (forcingCodet s) Q T ρ F M u) :
    IsForcingIterationCode (succ θ) (forcingIterationCodeNext θ s Q T ρ F M u) := by
  unfold forcingIterationCodeNext
  constructor
  · simpa only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
      forcingCodeE_code, forcingCodeL_code, forcingCodet_code] using h.system.extend c
  · simpa only [forcingCodeP_code] using (forcingFamilyNext_table _ _ _)
  · simpa only [forcingCodeR_code] using (forcingFamilyNext_table _ _ _)
  · simpa only [forcingCodeπ_code] using (forcingMatrixNext_table _ _ _ _)
  · simpa only [forcingCodeE_code] using (forcingMatrixNext_table _ _ _ _)
  · simpa only [forcingCodeL_code] using (forcingMatrixNext_table _ _ _ _)
  · simpa only [forcingCodet_code] using (forcingFamilyNext_table _ _ _)

structure ForcingCodeExtends (s z : V) : Prop where
  subP : forcingCodeP s ⊆ forcingCodeP z
  subR : forcingCodeR s ⊆ forcingCodeR z
  subπ : forcingCodeπ s ⊆ forcingCodeπ z
  subE : forcingCodeE s ⊆ forcingCodeE z
  subL : forcingCodeL s ⊆ forcingCodeL z
  subt : forcingCodet s ⊆ forcingCodet z

theorem ForcingCodeExtends.refl (s : V) : ForcingCodeExtends s s :=
  ⟨subset_refl _, subset_refl _, subset_refl _, subset_refl _, subset_refl _, subset_refl _⟩

theorem ForcingCodeExtends.trans {s z w : V}
    (h : ForcingCodeExtends s z) (k : ForcingCodeExtends z w) : ForcingCodeExtends s w := by
  constructor
  · exact fun x hx ↦ k.subP x (h.subP x hx)
  · exact fun x hx ↦ k.subR x (h.subR x hx)
  · exact fun x hx ↦ k.subπ x (h.subπ x hx)
  · exact fun x hx ↦ k.subE x (h.subE x hx)
  · exact fun x hx ↦ k.subL x (h.subL x hx)
  · exact fun x hx ↦ k.subt x (h.subt x hx)

theorem IsForcingIterationCode.extends_next {θ s : V} (h : IsForcingIterationCode θ s)
    (Q T ρ F M u : V) : ForcingCodeExtends s (forcingIterationCodeNext θ s Q T ρ F M u) := by
  unfold forcingIterationCodeNext
  constructor
  · simpa only [forcingCodeP_code] using (forcingFamilyNext_extends h.tableP _)
  · simpa only [forcingCodeR_code] using (forcingFamilyNext_extends h.tableR _)
  · simpa only [forcingCodeπ_code] using (forcingMatrixNext_extends h.tableπ _ _)
  · simpa only [forcingCodeE_code] using (forcingMatrixNext_extends h.tableE _ _)
  · simpa only [forcingCodeL_code] using (forcingMatrixNext_extends h.tableL _ _)
  · simpa only [forcingCodet_code] using (forcingFamilyNext_extends h.tablet _)

end ZFVP
