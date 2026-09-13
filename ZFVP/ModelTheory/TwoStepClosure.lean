import ZFVP.ModelTheory.ForcedSequenceBounds
import ZFVP.SetTheory.ForcingIterandFormula

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def twoStepClosedAtFormula : SetTheorySemisentence 7 :=
  f“P R o Q S t α. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingIterandFormula P R Q S t ∧ !IsOrdinal.dfn α ∧ !forcingClosedAtFormula P R α ∧
    (∀ p ∈ P, !(tripleForcingTruthFormula forcingClosedAtFormula) p P R Q S (!checkNameFormula o α)) →
    ∀ C T, !twoStepConditionsFormula C P R Q t → !twoStepOrderFormula T P R Q S t →
      !forcingClosedAtFormula C T α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStep_closedAt_countable [Countable V] {P R one Q S t α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (hbase : IsForcingClosedAt P R α)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingClosedAtFormula
      (standardTuple ![Q, S, checkName one α])) :
    IsForcingClosedAt (twoStepConditions P R Q t) (twoStepOrder P R Q S t) α := by
  intro f hf
  have hfi (i : V) (hi : i ∈ α) := function_value_mem hf.1 hi
  have hpi (i : V) (hi : i ∈ α) : kpair.π₁ (f ‘ i) ∈ P := by
    obtain ⟨a, ha, c, _, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    simpa only [he, kpair.π₁_kpair] using ha
  have hsi (i : V) (hi : i ∈ α) : kpair.π₂ (f ‘ i) ∈ twoStepNames Q t := by
    obtain ⟨a, _, c, hc, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    simpa only [he, kpair.π₂_kpair] using hc
  let b := definableGraph α (fun i ↦ kpair.π₁ (f ‘ i)) (by definability)
  let s := definableGraph α (fun i ↦ kpair.π₂ (f ‘ i)) (by definability)
  have hb (i : V) (hi : i ∈ α) : b ‘ i = kpair.π₁ (f ‘ i) := value_definableGraph _ _ _ hi
  have hs (i : V) (hi : i ∈ α) : s ‘ i = kpair.π₂ (f ‘ i) := value_definableGraph _ _ _ hi
  have hsd : domain s = α := domain_definableGraph _ _ _
  have hsn : IsNameSequence P s := by
    intro i hi
    rw [hs i (hsd ▸ hi)]
    exact h.name (hsi i (hsd ▸ hi))
  have hbdesc : IsForcingDescending P R α b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hpi, ?_⟩
    intro i hi j hj
    rw [hb i hi, hb j (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp (hf.2 i hi j hj)).2.2.1
  obtain ⟨p, hp, hpbound⟩ := hbase b hbdesc
  have hpbelow (i : V) (hi : i ∈ α) : ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R := by
    simpa only [hb i hi] using hpbound i hi
  let qn : ForcingName P := ⟨Q, h.posetName⟩
  let rn : ForcingName P := ⟨S, h.orderName⟩
  have ht : p ∈ forcingFormula P R forcingClosedAtFormula
      (standardTuple ![qn.val, rn.val, checkName one (domain s)]) := by
    simpa only [hsd] using htail p hp
  obtain ⟨r, hr, τ, hτ, hrp, hrτ, hrbound⟩ :=
      forced_sequence_lowerBound_countable hR htop qn rn hsn hp ht (by
    intro G hG hpG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hfirst (i : V) (hi : i ∈ α) : kpair.π₁ (f ‘ i) ∈ G :=
      hG.1.2.2.1 p hpG (kpair.π₁ (f ‘ i)) (hpi i hi) (hpbelow i hi)
    have hm (i : V) (hi : i ∈ domain s) : A.ofName ⟨s ‘ i, hsn i hi⟩ ∈ A.ofName qn := by
      have hiα : i ∈ α := hsd ▸ hi
      have hfmem : kpair.π₁ (f ‘ i) ∈ atomicMembership P R (s ‘ i) Q := by
        rw [hs i hiα]
        exact (mem_sep_iff.mp (hfi i hiα)).2
      have htmem : kpair.π₁ (f ‘ i) ∈ forcingFormula P R nameMemberFormula
          (standardTuple ![s ‘ i, Q]) := by rwa [forcingFormula_nameMember]
      have he := (A.formula_truth nameMemberFormula ![⟨s ‘ i, hsn i hi⟩, qn]).mpr
        ⟨kpair.π₁ (f ‘ i), hfirst i hiα, htmem⟩
      simpa [nameMemberFormula] using he
    refine ⟨A.sequenceValue_mem_function s hsn hm, ?_⟩
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := (A.mem_check_iff (domain s) x).mp hx
    obtain ⟨j, hj, rfl⟩ := (A.mem_check_iff i y).mp hy
    have hiα : i ∈ α := hsd ▸ hi
    have hjα : j ∈ α := IsOrdinal.toIsTransitive.mem_trans hj hiα
    have hjs : j ∈ domain s := hsd.symm ▸ hjα
    rw [A.sequenceValue_value s hsn hi, A.sequenceValue_value s hsn hjs]
    have ho := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp (hf.2 i hiα j hj)).2.2.2
    have ho' : kpair.π₁ (f ‘ i) ∈ forcingFormula P R boundedPairMemberFormula
        (standardTuple ![S, s ‘ i, s ‘ j]) := by simpa only [hs i hiα, hs j hjα] using ho
    exact (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula
      ![rn, ⟨s ‘ i, hsn i hi⟩, ⟨s ‘ j, hsn j hjs⟩]).mpr
      ⟨kpair.π₁ (f ‘ i), hfirst i hiα, ho'⟩))
  have hτnames : τ ∈ twoStepNames Q t := mem_union_iff.mpr (Or.inl hτ)
  have hcond : ⟨r, τ⟩ₖ ∈ twoStepConditions P R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hr, hτnames, hrτ⟩
  refine ⟨⟨r, τ⟩ₖ, hcond, fun i hi ↦ ?_⟩
  apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
  refine ⟨hcond, hfi i hi, ?_, ?_⟩
  · simpa only [kpair.π₁_kpair] using hR.2.2 r hr p hp (kpair.π₁ (f ‘ i)) (hpi i hi) hrp (hpbelow i hi)
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair, hs i hi] using hrbound i (hsd.symm ▸ hi)

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

theorem eval_twoStepClosedAtFormula (v : Fin 7 → V) : twoStepClosedAtFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingIterand (v 0) (v 1) (v 3) (v 4) (v 5) → IsOrdinal (v 6) →
      IsForcingClosedAt (v 0) (v 1) (v 6) →
      (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) forcingClosedAtFormula
        (standardTuple ![v 3, v 4, checkName (v 2) (v 6)])) →
      IsForcingClosedAt (twoStepConditions (v 0) (v 1) (v 3) (v 5))
        (twoStepOrder (v 0) (v 1) (v 3) (v 4) (v 5)) (v 6)) := by
  simp [twoStepClosedAtFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_six_eq, forall_three_eq, forall_five_eq]

private theorem twoStepClosedAt_valid (v : Fin 7 → V) : twoStepClosedAtFormula.Evalb v := by
  apply eval_of_countable_zf twoStepClosedAtFormula
  intro W _ _ _ _ w
  apply (eval_twoStepClosedAtFormula w).mpr
  intro hR htop h hα hbase htail
  let := hα
  exact twoStep_closedAt_countable hR htop h hbase htail

private theorem twoStepClosedAt_transfer (v : Fin 7 → V)
    (hR : IsForcingPreorder (v 0) (v 1)) (htop : IsForcingTop (v 0) (v 1) (v 2))
    (h : IsForcingIterand (v 0) (v 1) (v 3) (v 4) (v 5)) (hα : IsOrdinal (v 6))
    (hbase : IsForcingClosedAt (v 0) (v 1) (v 6))
    (htail : ∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) forcingClosedAtFormula
      (standardTuple ![v 3, v 4, checkName (v 2) (v 6)])) :
    IsForcingClosedAt (twoStepConditions (v 0) (v 1) (v 3) (v 5))
      (twoStepOrder (v 0) (v 1) (v 3) (v 4) (v 5)) (v 6) :=
  (eval_twoStepClosedAtFormula v).mp (twoStepClosedAt_valid v) hR htop h hα hbase htail

theorem twoStep_closedAt {P R one Q S t α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (hbase : IsForcingClosedAt P R α)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingClosedAtFormula
      (standardTuple ![Q, S, checkName one α])) :
    IsForcingClosedAt (twoStepConditions P R Q t) (twoStepOrder P R Q S t) α := by
  exact twoStepClosedAt_transfer ![P, R, one, Q, S, t, α] hR htop h (show IsOrdinal α from inferInstance) hbase htail

theorem twoStep_closedBelow {P R one Q S t κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (hbase : IsForcingClosedBelow P R κ)
    (htail : ∀ α ∈ κ, ∀ p ∈ P, p ∈ forcingFormula P R forcingClosedAtFormula
      (standardTuple ![Q, S, checkName one α])) :
    IsForcingClosedBelow (twoStepConditions P R Q t) (twoStepOrder P R Q S t) κ := by
  intro α hα
  let := IsOrdinal.of_mem hα
  exact twoStep_closedAt hR htop h (hbase α hα) (htail α hα)

end ZFVP


