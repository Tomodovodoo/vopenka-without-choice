import ZFVP.ModelTheory.RankSaturatedHartogsStage
import ZFVP.ModelTheory.SaturatedHartogsStage
import ZFVP.SetTheory.BoundedDomainParameters
import ZFVP.ModelTheory.CountableZFTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankSaturatedHartogsStageAtConclusionFormula : SetTheorySemisentence 7 :=
  let φ := boundedDomainParametersFormula saturatedHartogsStageAtFormula
  let ψ := saturatedHartogsStageAtFormula.subst (fun i ↦ .bvar i.succ)
  φ 🡘 ψ

def rankSaturatedHartogsStageAtAgreementFormula : SetTheorySemisentence 8 :=
  f“U ξ P R o κ γ z. U = !hierarchyFormula ξ ∧ !choicelessInaccessibleFormula ξ ∧
    P ∈ U ∧ R ∈ U ∧ o ∈ U ∧ κ ∈ U ∧ γ ∈ U ∧ z ∈ U ∧
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ !IsOrdinal.dfn γ →
      !rankSaturatedHartogsStageAtConclusionFormula U z P R o κ γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance rankSaturatedHartogsStageAtConclusionFormula_defined :
    Defined (fun v : Fin 7 → V ↦
      (boundedDomainParametersFormula saturatedHartogsStageAtFormula).Evalb v ↔
        v 1 = saturatedHartogsStageAt (v 2) (v 3) (v 4) (v 5) (v 6))
      rankSaturatedHartogsStageAtConclusionFormula :=
  ⟨fun v ↦ by simp [rankSaturatedHartogsStageAtConclusionFormula, Semiformula.eval_substs]⟩

private theorem forall_seven_eq_hartogsStage {W : Type*} (a b c d e f g : W)
    (F : W → W → W → W → W → W → W → Prop) :
    (∀ u v w x y z t, u = a → v = b → w = c → x = d → y = e → z = f → t = g → F u v w x y z t) ↔
      F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z t hu hv hw hx hy hz ht ↦ by subst u v w x y z t; exact h⟩

private theorem forall_three_eq_hartogsStage {W : Type*} (a b c : W) (F : W → W → W → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

theorem eval_rankSaturatedHartogsStageAtAgreementFormula (v : Fin 8 → V) :
    rankSaturatedHartogsStageAtAgreementFormula.Evalb v ↔
      (v 0 = hierarchy (v 1) → IsChoicelessInaccessible (v 1) →
        v 2 ∈ v 0 → v 3 ∈ v 0 → v 4 ∈ v 0 → v 5 ∈ v 0 → v 6 ∈ v 0 → v 7 ∈ v 0 →
        IsForcingPreorder (v 2) (v 3) → IsForcingTop (v 2) (v 3) (v 4) → IsOrdinal (v 6) →
        ((boundedDomainParametersFormula saturatedHartogsStageAtFormula).Evalb ![v 0, v 7, v 2, v 3, v 4, v 5, v 6] ↔
          v 7 = saturatedHartogsStageAt (v 2) (v 3) (v 4) (v 5) (v 6))) := by
  simp [rankSaturatedHartogsStageAtAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_seven_eq_hartogsStage, forall_three_eq_hartogsStage]

theorem rankSaturatedHartogsStageAtAgreement_countable [Countable V] (v : Fin 8 → V) :
    rankSaturatedHartogsStageAtAgreementFormula.Evalb v := by
  apply (eval_rankSaturatedHartogsStageAtAgreementFormula v).mpr
  intro hU hξ hP hR ho hk hg hz hord htop hγ
  rw [hU] at hP hR ho hk hg hz ⊢
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive (v 1)
  let P : SetDomain (hierarchy (v 1)) := ⟨v 2, hP⟩
  let R : SetDomain (hierarchy (v 1)) := ⟨v 3, hR⟩
  let o : SetDomain (hierarchy (v 1)) := ⟨v 4, ho⟩
  let k : SetDomain (hierarchy (v 1)) := ⟨v 5, hk⟩
  let g : SetDomain (hierarchy (v 1)) := ⟨v 6, hg⟩
  let z : SetDomain (hierarchy (v 1)) := ⟨v 7, hz⟩
  have he := rank_saturatedHartogsStageAt_val_countable hξ P R o k g
    ((TransitiveZF.forcingPreorder_iff (hierarchy (v 1)) P R).mpr hord)
    ((TransitiveZF.forcingTop_iff (hierarchy (v 1)) P R o).mpr htop)
    ((TransitiveZF.ordinal_iff (hierarchy (v 1)) g).mpr hγ)
  have hb := eval_boundedDomainParametersFormula saturatedHartogsStageAtFormula (hierarchy (v 1)) ![z, P, R, o, k, g]
  have hv : (fun i : Fin 6 ↦ ((![z, P, R, o, k, g] : Fin 6 → SetDomain (hierarchy (v 1))) i).val) =
      ![v 7, v 2, v 3, v 4, v 5, v 6] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.cases rfl
        (fun t ↦ Fin.elim0 t) n) m) l) k) j) i
  rw [hv] at hb
  have heq : z = saturatedHartogsStageAt P R o k g ↔ v 7 = saturatedHartogsStageAt (v 2) (v 3) (v 4) (v 5) (v 6) := by
    constructor
    · intro h
      exact (congrArg Subtype.val h).trans he
    · intro h
      exact Subtype.ext (h.trans he.symm)
  exact hb.trans ((Defined.eval_iff (φ := saturatedHartogsStageAtFormula) ![z, P, R, o, k, g]).trans heq)

theorem rank_saturatedHartogsStageAt_val {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hξ : IsChoicelessInaccessible ξ) (P R one κ γ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hγ : IsOrdinal γ) :
    (saturatedHartogsStageAt P R one κ γ).val = saturatedHartogsStageAt P.val R.val one.val κ.val γ.val := by
  let := hierarchy_transitive ξ
  let z := saturatedHartogsStageAt P R one κ γ
  have hv := eval_of_countable_zf rankSaturatedHartogsStageAtAgreementFormula
    (fun _ _ _ _ _ v ↦ rankSaturatedHartogsStageAtAgreement_countable v)
    ![hierarchy ξ, ξ, P.val, R.val, one.val, κ.val, γ.val, z.val]
  have he := (eval_rankSaturatedHartogsStageAtAgreementFormula _).mp hv rfl hξ P.property R.property
    one.property κ.property γ.property z.property
    ((TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mp hR)
    ((TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mp ht)
    ((TransitiveZF.ordinal_iff (hierarchy ξ) γ).mp hγ)
  apply he.mp
  have hb := eval_boundedDomainParametersFormula saturatedHartogsStageAtFormula (hierarchy ξ) ![z, P, R, one, κ, γ]
  have hn : (fun i : Fin 6 ↦ ((![z, P, R, one, κ, γ] : Fin 6 → SetDomain (hierarchy ξ)) i).val) =
      ![z.val, P.val, R.val, one.val, κ.val, γ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.cases rfl
        (fun t ↦ Fin.elim0 t) n) m) l) k) j) i
  rw [hn] at hb
  exact hb.mpr ((Defined.eval_iff (φ := saturatedHartogsStageAtFormula) ![z, P, R, one, κ, γ]).mpr rfl)

end ZFVP
