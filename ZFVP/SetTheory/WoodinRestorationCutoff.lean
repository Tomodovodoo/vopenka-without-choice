import ZFVP.ModelTheory.WoodinSupercompactRestoration
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.LeastOrdinalChoice

/-! Least inaccessible local restoration cutoffs. These are computed in one
ZF model. Applying this selection inside an iterated forcing extension still
requires the two-step forcing construction and its preservation theorems. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinRestorationCutoffFormula : SetTheorySemisentence 2 :=
  f“κ δ. κ ∈ δ ∧ !choicelessInaccessibleFormula δ ∧ ∃ P R,
    !woodinCollapseSetFormula P κ δ ∧ !piOneReverseInclusionOrderFormula R P ∧
    ∀ p ∈ P, !(checkedUnaryForcingFormula dependentChoiceBelowFormula) P R (!isEmpty) p δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinRestorationCutoff (κ δ : V) : Prop :=
  κ ∈ δ ∧ IsChoicelessInaccessible δ ∧ ∀ p ∈ woodinCollapse κ δ,
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ])

theorem eval_woodinRestorationCutoffFormula (κ δ : V) :
    woodinRestorationCutoffFormula.Evalb ![κ, δ] ↔ IsWoodinRestorationCutoff κ δ := by
  simp only [woodinRestorationCutoffFormula, IsWoodinRestorationCutoff]
  simp [eval_piOneReverseInclusionOrderFormula, woodinCollapseOrder]
  intro _ hd
  exact fun _ ↦ hd.1

instance woodinRestorationCutoffFormula_defined :
    ℒₛₑₜ-relation[V] IsWoodinRestorationCutoff via woodinRestorationCutoffFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv]
  exact eval_woodinRestorationCutoffFormula _ _

instance woodinRestorationCutoff_definable : ℒₛₑₜ-relation[V] IsWoodinRestorationCutoff :=
  woodinRestorationCutoffFormula_defined.to_definable

theorem IsWoodinSupercompact.restorationCutoff {κ δ : V} (hδ : IsWoodinSupercompact δ)
    (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    IsWoodinRestorationCutoff κ δ :=
  ⟨hκδ, hδ.inaccessible, fun _ hp ↦ woodinSupercompact_collapse_forces_restoration hκ hδ hκδ hDC hp⟩

noncomputable def woodinRestorationCutoff (κ : V) : V :=
  leastOrdinalOrZero IsWoodinRestorationCutoff (by definability) κ

instance woodinRestorationCutoff_function_definable : ℒₛₑₜ-function₁[V] woodinRestorationCutoff := by
  unfold woodinRestorationCutoff
  infer_instance

instance woodinRestorationCutoff_ordinal (κ : V) : IsOrdinal (woodinRestorationCutoff κ) := by
  unfold woodinRestorationCutoff
  infer_instance

theorem woodinRestorationCutoff_spec {κ δ : V} (hδ : IsWoodinRestorationCutoff κ δ) :
    IsLeastOrdinal (IsWoodinRestorationCutoff κ) (woodinRestorationCutoff κ) :=
  leastOrdinalOrZero_spec _ _ κ ⟨δ, hδ.2.1.1, hδ⟩

theorem woodinRestorationCutoff_le {κ δ : V} (hδ : IsWoodinRestorationCutoff κ δ) :
    woodinRestorationCutoff κ ⊆ δ := (woodinRestorationCutoff_spec hδ).2.2 δ hδ.2.1.1 hδ

theorem woodinRestorationCutoff_exists_of_supercompact {κ δ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsWoodinSupercompact δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    κ ∈ woodinRestorationCutoff κ ∧ woodinRestorationCutoff κ ⊆ δ ∧
      IsChoicelessInaccessible (woodinRestorationCutoff κ) ∧
      IsRegularCardinal (woodinRestorationCutoff κ) ∧
      IsInternalZFModel (hierarchy (woodinRestorationCutoff κ)) ∧
      IsWoodinRestorationCutoff κ (woodinRestorationCutoff κ) := by
  have hd := hδ.restorationCutoff hκ hκδ hDC
  have h := (woodinRestorationCutoff_spec hd).2.1
  exact ⟨h.1, woodinRestorationCutoff_le hd, h.2.1, h.2.1.regular, h.2.1.internalZFModel, h⟩

theorem IsWoodinRestorationCutoff.dependentChoice {κ δ : V}
    (hδ : IsWoodinRestorationCutoff κ δ) (hκ : IsRegularCardinal κ) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∀ η ∈ (woodinCollapseContext hκ δ G hG).check δ, InternalDependentChoiceAt η := by
  let S := woodinCollapseContext hκ δ G hG
  let c : ForcingName S.P := ⟨checkName ∅ δ, checkName_isName (empty_mem_woodinCollapse (hκ.2.1 ∅ (by simp)) δ) δ⟩
  obtain ⟨p, hpG⟩ := hG.1.2.1
  have h := (S.formula_truth dependentChoiceBelowFormula ![c]).mpr
    ⟨p, hpG, hδ.2.2 p (hG.1.1 p hpG)⟩
  exact (Defined.eval_iff _).mp h

end ZFVP
