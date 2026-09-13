import ZFVP.ModelTheory.ProjectionQuotientClosureTransport
import ZFVP.ModelTheory.ProjectionQuotientSeparative
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.ModelTheory.SeparativeGeneric
import ZFVP.ModelTheory.ProjectionQuotientDensity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSeparativeBoundFormula : SetTheorySemisentence 5 :=
  f“P R α f q. q ∈ P ∧ ∃ S, !forcingSeparativeOrderFormula S P R ∧
    ∀ i ∈ α, !kpair.dfn q (!value.dfn f i) ∈ S”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSeparativeBoundFormula_defined :
    Defined (fun v : Fin 5 → V ↦ v 4 ∈ v 0 ∧
      ∀ i ∈ v 2, ⟨v 4, (v 3) ‘ i⟩ₖ ∈ forcingSeparativeOrder (v 0) (v 1))
      forcingSeparativeBoundFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeBoundFormula]⟩

/-- Separative closure composes through a projection when every actual quotient
extension has the required closure. This version uses external generics over a
countable ground model. -/
theorem projection_separative_closedAt_countable [Countable V]
    {P R one Q S π α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbase : IsForcingClosedAt P (forcingSeparativeOrder P R) α)
    (htail : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      IsForcingClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
        (A.check α)) :
    IsForcingClosedAt Q (forcingSeparativeOrder Q S) α := by
  intro f hf
  let := IsFunction.of_mem hf.1
  have hpdesc : IsForcingDescending P (forcingSeparativeOrder P R) α (compose f π) := by
    refine ⟨compose_function hf.1 hπ.maps, ?_⟩
    intro i hi j hj
    rw [value_compose_of_mem_function hf.1 hπ.maps hi,
      value_compose_of_mem_function hf.1 hπ.maps (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact hπ.separative_monotone (hf.2 i hi j hj)
  obtain ⟨p, hp, hpb⟩ := hbase _ hpdesc
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hfi (i : V) (hi : i ∈ α) : A.check (f ‘ i) ∈ A.projectionQuotient Q π := by
    apply (A.check_mem_projectionQuotient_iff hπ.maps).mpr
    refine ⟨function_value_mem hf.1 hi, externalForcingGeneric_separative_upward hR hG hpG ?_⟩
    simpa only [value_compose_of_mem_function hf.1 hπ.maps hi] using hpb i hi
  have hval (i : V) (hi : i ∈ α) : (A.check f) ‘ (A.check i) = A.check (f ‘ i) :=
    A.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hi)
  let g : A.Model := definableGraph (A.check α) (fun i ↦ (A.check f) ‘ i) (by definability)
  have hgv (i : A.Model) (hi : i ∈ A.check α) : g ‘ i = (A.check f) ‘ i :=
    value_definableGraph _ _ _ hi
  have hg : IsForcingDescending (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
      (A.check α) g := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ ?_, ?_⟩
    · intro i hi
      obtain ⟨i, hi', rfl⟩ := (A.mem_check_iff α i).mp hi
      rw [hval i hi']
      exact hfi i hi'
    · intro i hi j hj
      obtain ⟨i, hi', rfl⟩ := (A.mem_check_iff α i).mp hi
      obtain ⟨j, hj', rfl⟩ := (A.mem_check_iff i j).mp hj
      have hjα := IsOrdinal.toIsTransitive.mem_trans hj' hi'
      rw [hgv _ hi, hgv _ ((A.check_mem_iff j α).mpr hjα), hval i hi', hval j hjα]
      exact A.projectionQuotient_separative_of_ground hπ hS (hfi i hi') (hfi j hjα) (hf.2 i hi' j hj')
  obtain ⟨x, hx, hxb⟩ := htail G hG g hg
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
  let QN : ForcingName P := ⟨projectionQuotientName Q π one, projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one,
    projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  let cn (x : V) : ForcingName P := ⟨checkName one x, checkName_isName htop.1 x⟩
  have hev : forcingSeparativeBoundFormula.Evalb
      (fun i ↦ A.ofName (![QN, SN, cn α, cn f, cn q] i)) := by
    apply (Defined.eval_iff _).mpr
    change A.check q ∈ A.ofName QN ∧ ∀ i ∈ A.check α,
      ⟨A.check q, (A.check f) ‘ i⟩ₖ ∈ forcingSeparativeOrder (A.ofName QN) (A.ofName SN)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
    exact ⟨hx, fun i hi ↦ hgv i hi ▸ hxb i hi⟩
  obtain ⟨a, haG, haf⟩ := (A.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, cn α, cn f, cn q]).mp hev
  obtain ⟨b, hbG, hba, hbq⟩ := hG.1.2.2.2 a haG _ hqG
  obtain ⟨u, hu, huq, heu⟩ := hπ.lift q hq b (hG.1.1 b hbG) hbq
  refine ⟨u, hu, ?_⟩
  intro i hi
  refine (kpair_mem_forcingSeparativeOrder Q S u (f ‘ i)).mpr
    ⟨hu, function_value_mem hf.1 hi, ?_⟩
  intro s hs hsu
  obtain ⟨H, hH, hsH⟩ := exists_externalForcingGeneric hR (function_value_mem hπ.maps hs)
  let B : ForcingContext V := ⟨P, R, one, H, hR, htop, hH⟩
  have hsa : ⟨π ‘ s, a⟩ₖ ∈ R := by
    have hsb := hπ.monotone s hs u hu hsu
    rw [heu] at hsb
    exact hR.2.2 _ (function_value_mem hπ.maps hs) b (hG.1.1 b hbG) a (hG.1.1 a haG) hsb hba
  have haH := hH.1.2.2.1 _ hsH a (hG.1.1 a haG) hsa
  have hb := (Defined.eval_iff _).mp ((B.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, cn α, cn f, cn q]).mpr ⟨a, haH, haf⟩)
  change B.check q ∈ B.ofName QN ∧ ∀ j ∈ B.check α,
    ⟨B.check q, (B.check f) ‘ j⟩ₖ ∈ forcingSeparativeOrder (B.ofName QN) (B.ofName SN) at hb
  rw [B.ofName_projectionQuotient hπ.maps, B.ofName_projectionQuotientOrder hπ hS] at hb
  have hbi := hb.2 (B.check i) ((B.check_mem_iff i α).mpr hi)
  rw [B.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hi)] at hbi
  have hs' := (B.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hs, hsH⟩
  have hsq' : ⟨B.check s, B.check q⟩ₖ ∈ B.projectionQuotientOrder Q S π :=
    (B.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨B.check_kpair s q ▸ (B.check_mem_iff _ _).mpr (hS.2.2 s hs u hu q hq hsu huq), hs', hb.1⟩
  obtain ⟨y, hy, hys, hyi⟩ := ((kpair_mem_forcingSeparativeOrder _ _ _ _).mp hbi).2.2 _ hs' hsq'
  obtain ⟨v, hv, _, rfl⟩ := (B.mem_projectionQuotient_iff hπ.maps y).mp hy
  have hvs := ((B.projectionQuotientOrder_pair_iff Q S π _ _).mp hys).1
  have hvi := ((B.projectionQuotientOrder_pair_iff Q S π _ _).mp hyi).1
  rw [← B.check_kpair, B.check_mem_iff] at hvs hvi
  exact ⟨v, hv, hvs, hvi⟩

theorem projection_separative_closedAt_of_forced_countable [Countable V]
    {P R one Q S π α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbase : IsForcingClosedAt P (forcingSeparativeOrder P R) α)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingSeparativeClosedAtFormula
      (standardTuple ![projectionQuotientName Q π one,
        projectionQuotientOrderName S π one, checkName one α])) :
    IsForcingClosedAt Q (forcingSeparativeOrder Q S) α := by
  apply projection_separative_closedAt_countable hR htop hπ hS hbase
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let QN : ForcingName P := ⟨projectionQuotientName Q π one,
    projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one,
    projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  obtain ⟨p, hp⟩ := hG.1.2.1
  have ht := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeClosedAtFormula
    ![QN, SN, ⟨checkName one α, checkName_isName htop.1 α⟩]).mpr
      ⟨p, hp, htail p (hG.1.1 p hp)⟩)
  change IsForcingClosedAt (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
    (A.check α) at ht
  rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at ht
  exact ht

def projectionSeparativeClosedAtFormula : SetTheorySemisentence 7 :=
  f“P R o Q S π α. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingProjectionFormula P R Q S π ∧ !forcingPreorderFormula Q S ∧
    !IsOrdinal.dfn α ∧ !forcingSeparativeClosedAtFormula P R α ∧
    (∀ p ∈ P, !(tripleForcingTruthFormula forcingSeparativeClosedAtFormula) p P R
      (!projectionQuotientNameFormula Q π o) (!projectionQuotientOrderNameFormula S π o)
      (!checkNameFormula o α)) → !forcingSeparativeClosedAtFormula Q S α”

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

theorem eval_projectionSeparativeClosedAtFormula (v : Fin 7 → V) :
    projectionSeparativeClosedAtFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingProjection (v 0) (v 1) (v 3) (v 4) (v 5) →
        IsForcingPreorder (v 3) (v 4) → IsOrdinal (v 6) →
        IsForcingClosedAt (v 0) (forcingSeparativeOrder (v 0) (v 1)) (v 6) →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) forcingSeparativeClosedAtFormula
          (standardTuple ![projectionQuotientName (v 3) (v 5) (v 2),
            projectionQuotientOrderName (v 4) (v 5) (v 2), checkName (v 2) (v 6)])) →
        IsForcingClosedAt (v 3) (forcingSeparativeOrder (v 3) (v 4)) (v 6)) := by
  simp [projectionSeparativeClosedAtFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_three_eq, forall_five_eq, forall_six_eq]

private theorem projectionSeparativeClosedAt_valid (v : Fin 7 → V) :
    projectionSeparativeClosedAtFormula.Evalb v := by
  apply eval_of_countable_zf projectionSeparativeClosedAtFormula
  intro W _ _ _ _ w
  apply (eval_projectionSeparativeClosedAtFormula w).mpr
  intro hR htop hπ hS hα hbase htail
  let := hα
  exact projection_separative_closedAt_of_forced_countable hR htop hπ hS hbase htail

theorem projection_separative_closedAt_of_forced
    {P R one Q S π α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbase : IsForcingClosedAt P (forcingSeparativeOrder P R) α)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingSeparativeClosedAtFormula
      (standardTuple ![projectionQuotientName Q π one,
        projectionQuotientOrderName S π one, checkName one α])) :
    IsForcingClosedAt Q (forcingSeparativeOrder Q S) α :=
  (eval_projectionSeparativeClosedAtFormula ![P, R, one, Q, S, π, α]).mp
    (projectionSeparativeClosedAt_valid _) hR htop hπ hS (show IsOrdinal α from inferInstance) hbase htail

theorem projection_separative_closedBelow_of_forced
    {P R one Q S π κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbase : IsForcingClosedBelow P (forcingSeparativeOrder P R) κ)
    (htail : ∀ α ∈ κ, ∀ p ∈ P, p ∈ forcingFormula P R forcingSeparativeClosedAtFormula
      (standardTuple ![projectionQuotientName Q π one,
        projectionQuotientOrderName S π one, checkName one α])) :
    IsForcingClosedBelow Q (forcingSeparativeOrder Q S) κ := by
  intro α hα
  let := IsOrdinal.of_mem hα
  exact projection_separative_closedAt_of_forced hR htop hπ hS (hbase α hα) (htail α hα)

end ZFVP
