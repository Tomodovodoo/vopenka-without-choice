import ZFVP.ModelTheory.ForcedSequenceBounds
import ZFVP.SetTheory.ForcingIterandFormula
import ZFVP.SetTheory.ForcingDirectedClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingDirectedClosedAtFormula : SetTheorySemisentence 3 :=
  f“P R I. ∀ s, (s ∈ !function.dfn P I ∧ ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I,
    !kpair.dfn (!value.dfn s k) (!value.dfn s i) ∈ R ∧
    !kpair.dfn (!value.dfn s k) (!value.dfn s j) ∈ R) →
    ∃ p ∈ P, ∀ i ∈ I, !kpair.dfn p (!value.dfn s i) ∈ R”

@[irreducible] def twoStepDirectedClosedAtFormula : SetTheorySemisentence 7 :=
  f“P R o Q S t I. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingIterandFormula P R Q S t ∧ !forcingDirectedClosedAtFormula P R I ∧
    (∀ p ∈ P, !(tripleForcingTruthFormula forcingDirectedClosedAtFormula) p P R Q S (!checkNameFormula o I)) →
    ∀ C T, !twoStepConditionsFormula C P R Q t → !twoStepOrderFormula T P R Q S t →
      !forcingDirectedClosedAtFormula C T I”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingDirectedClosedAtFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingDirectedClosedAt via forcingDirectedClosedAtFormula :=
  ⟨fun v ↦ by simp [forcingDirectedClosedAtFormula, IsForcingDirectedClosedAt, IsForcingDirectedFamily]⟩

theorem twoStep_directedClosedAt_countable [Countable V] {P R one Q S t I : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (hbase : IsForcingDirectedClosedAt P R I)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingDirectedClosedAtFormula
      (standardTuple ![Q, S, checkName one I])) :
    IsForcingDirectedClosedAt (twoStepConditions P R Q t) (twoStepOrder P R Q S t) I := by
  intro f hf
  have hfi (i : V) (hi : i ∈ I) := function_value_mem hf.1 hi
  have hpi (i : V) (hi : i ∈ I) : kpair.π₁ (f ‘ i) ∈ P := by
    obtain ⟨a, ha, c, _, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    simpa only [he, kpair.π₁_kpair] using ha
  have hsi (i : V) (hi : i ∈ I) : kpair.π₂ (f ‘ i) ∈ twoStepNames Q t := by
    obtain ⟨a, _, c, hc, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp (hfi i hi)).1
    simpa only [he, kpair.π₂_kpair] using hc
  let b := definableGraph I (fun i ↦ kpair.π₁ (f ‘ i)) (by definability)
  let s := definableGraph I (fun i ↦ kpair.π₂ (f ‘ i)) (by definability)
  have hb (i : V) (hi : i ∈ I) : b ‘ i = kpair.π₁ (f ‘ i) := value_definableGraph _ _ _ hi
  have hs (i : V) (hi : i ∈ I) : s ‘ i = kpair.π₂ (f ‘ i) := value_definableGraph _ _ _ hi
  have hsd : domain s = I := domain_definableGraph _ _ _
  have hsn : IsNameSequence P s := by
    intro i hi
    rw [hs i (hsd ▸ hi)]
    exact h.name (hsi i (hsd ▸ hi))
  have hbdir : IsForcingDirectedFamily P R I b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hpi, ?_⟩
    intro i hi j hj
    obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hb k hk, hb i hi]
      exact ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hki).2.2.1
    · rw [hb k hk, hb j hj]
      exact ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hkj).2.2.1
  obtain ⟨p, hp, hpbound⟩ := hbase b hbdir
  have hpbelow (i : V) (hi : i ∈ I) : ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R := by
    simpa only [hb i hi] using hpbound i hi
  let qn : ForcingName P := ⟨Q, h.posetName⟩
  let rn : ForcingName P := ⟨S, h.orderName⟩
  obtain ⟨r, hr, τ, hτ, hrp, hrτ, hrbound⟩ :=
      forced_sequence_lowerBound_of_generics_countable hR htop qn rn hsn hp (by
    intro G hG hpG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    let c : ForcingName P := ⟨checkName one I, checkName_isName htop.1 I⟩
    have hc : IsForcingDirectedClosedAt (A.ofName qn) (A.ofName rn) (A.check I) :=
      (Defined.eval_iff _).mp ((A.formula_truth forcingDirectedClosedAtFormula ![qn, rn, c]).mpr
        ⟨p, hpG, htail p hp⟩)
    rw [hsd]
    apply hc (A.sequenceValue s hsn)
    have hfirst (i : V) (hi : i ∈ I) : kpair.π₁ (f ‘ i) ∈ G :=
      hG.1.2.2.1 p hpG (kpair.π₁ (f ‘ i)) (hpi i hi) (hpbelow i hi)
    have hm (i : V) (hi : i ∈ domain s) : A.ofName ⟨s ‘ i, hsn i hi⟩ ∈ A.ofName qn := by
      have hiI : i ∈ I := hsd ▸ hi
      have hfmem : kpair.π₁ (f ‘ i) ∈ atomicMembership P R (s ‘ i) Q := by
        rw [hs i hiI]
        exact (mem_sep_iff.mp (hfi i hiI)).2
      have htmem : kpair.π₁ (f ‘ i) ∈ forcingFormula P R nameMemberFormula
          (standardTuple ![s ‘ i, Q]) := by rwa [forcingFormula_nameMember]
      have he := (A.formula_truth nameMemberFormula ![⟨s ‘ i, hsn i hi⟩, qn]).mpr
        ⟨kpair.π₁ (f ‘ i), hfirst i hiI, htmem⟩
      simpa [nameMemberFormula] using he
    refine ⟨?_, ?_⟩
    · simpa only [hsd] using A.sequenceValue_mem_function s hsn hm
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := (A.mem_check_iff I x).mp hx
      obtain ⟨j, hj, rfl⟩ := (A.mem_check_iff I y).mp hy
      obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
      refine ⟨A.check k, (A.check_mem_iff _ _).mpr hk, ?_, ?_⟩
      all_goals
        rw [A.sequenceValue_value s hsn (hsd.symm ▸ hk), A.sequenceValue_value s hsn (hsd.symm ▸ ‹_ ∈ I›)]
      · have ho := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hki).2.2.2
        have ho' : kpair.π₁ (f ‘ k) ∈ forcingFormula P R boundedPairMemberFormula
            (standardTuple ![S, s ‘ k, s ‘ i]) := by simpa only [hs k hk, hs i hi] using ho
        exact (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula
          ![rn, ⟨s ‘ k, hsn k (hsd.symm ▸ hk)⟩, ⟨s ‘ i, hsn i (hsd.symm ▸ hi)⟩]).mpr
          ⟨kpair.π₁ (f ‘ k), hfirst k hk, ho'⟩)
      · have ho := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hkj).2.2.2
        have ho' : kpair.π₁ (f ‘ k) ∈ forcingFormula P R boundedPairMemberFormula
            (standardTuple ![S, s ‘ k, s ‘ j]) := by simpa only [hs k hk, hs j hj] using ho
        exact (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula
          ![rn, ⟨s ‘ k, hsn k (hsd.symm ▸ hk)⟩, ⟨s ‘ j, hsn j (hsd.symm ▸ hj)⟩]).mpr
          ⟨kpair.π₁ (f ‘ k), hfirst k hk, ho'⟩))
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

theorem eval_twoStepDirectedClosedAtFormula (v : Fin 7 → V) : twoStepDirectedClosedAtFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingIterand (v 0) (v 1) (v 3) (v 4) (v 5) →
      IsForcingDirectedClosedAt (v 0) (v 1) (v 6) →
      (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) forcingDirectedClosedAtFormula
        (standardTuple ![v 3, v 4, checkName (v 2) (v 6)])) →
      IsForcingDirectedClosedAt (twoStepConditions (v 0) (v 1) (v 3) (v 5))
        (twoStepOrder (v 0) (v 1) (v 3) (v 4) (v 5)) (v 6)) := by
  simp [twoStepDirectedClosedAtFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_six_eq, forall_three_eq, forall_five_eq]

private theorem twoStepDirectedClosedAt_valid (v : Fin 7 → V) : twoStepDirectedClosedAtFormula.Evalb v := by
  apply eval_of_countable_zf twoStepDirectedClosedAtFormula
  intro W _ _ _ _ w
  apply (eval_twoStepDirectedClosedAtFormula w).mpr
  exact fun hR htop h hbase htail ↦ twoStep_directedClosedAt_countable hR htop h hbase htail

private theorem twoStepDirectedClosedAt_transfer (v : Fin 7 → V)
    (hR : IsForcingPreorder (v 0) (v 1)) (htop : IsForcingTop (v 0) (v 1) (v 2))
    (h : IsForcingIterand (v 0) (v 1) (v 3) (v 4) (v 5))
    (hbase : IsForcingDirectedClosedAt (v 0) (v 1) (v 6))
    (htail : ∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) forcingDirectedClosedAtFormula
      (standardTuple ![v 3, v 4, checkName (v 2) (v 6)])) :
    IsForcingDirectedClosedAt (twoStepConditions (v 0) (v 1) (v 3) (v 5))
      (twoStepOrder (v 0) (v 1) (v 3) (v 4) (v 5)) (v 6) :=
  (eval_twoStepDirectedClosedAtFormula v).mp (twoStepDirectedClosedAt_valid v) hR htop h hbase htail

theorem twoStep_directedClosedAt {P R one Q S t I : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (hbase : IsForcingDirectedClosedAt P R I)
    (htail : ∀ p ∈ P, p ∈ forcingFormula P R forcingDirectedClosedAtFormula
      (standardTuple ![Q, S, checkName one I])) :
    IsForcingDirectedClosedAt (twoStepConditions P R Q t) (twoStepOrder P R Q S t) I :=
  twoStepDirectedClosedAt_transfer ![P, R, one, Q, S, t, I] hR htop h hbase htail

end ZFVP
