import ZFVP.ModelTheory.ForcingLocalCanonicalName
import ZFVP.SetTheory.UniformFormulaName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def forcingCarrierAtomsFormula : SetTheorySemisentence 4 :=
  f“C P R Q. C = !domain.dfn (!forcingUnionNameFormula P R Q)”

def forcingCarrierPoolFormula : SetTheorySemisentence 4 :=
  f“U P R Q. U = !power.dfn (!prod.dfn (!forcingCarrierAtomsFormula P R Q) P)”

def forcingCarrierNormalizeFormula : SetTheorySemisentence 5 :=
  f“N P R Q t. !forcingSaturatedNameFormula N P R (!forcingCarrierAtomsFormula P R Q) t”

def forcingCarrierLocalNormalizeFormula : SetTheorySemisentence 6 :=
  f“N P R Q p t. !forcingRestrictedNameFormula N P R p (!forcingCarrierNormalizeFormula P R Q t)”

def forcingCarrierNormalizeCorrectFormula : SetTheorySemisentence 6 :=
  f“P R o Q t p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P t ∧ p ∈ P ∧
    p ∈ !atomicMembershipFormula P R t Q →
      p ∈ !atomicEqualityFormula P R (!forcingCarrierNormalizeFormula P R Q t) t”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingCarrierAtoms (P R Q : V) : V := domain (forcingUnionName P R Q)

noncomputable def forcingCarrierPool (P R Q : V) : V := ℘ (forcingCarrierAtoms P R Q ×ˢ P)

noncomputable def forcingCarrierNormalize (P R Q τ : V) : V :=
  forcingSaturatedName P R (forcingCarrierAtoms P R Q) τ

noncomputable def forcingCarrierLocalNormalize (P R Q p τ : V) : V :=
  forcingRestrictedName P R p (forcingCarrierNormalize P R Q τ)

instance forcingCarrierAtomsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingCarrierAtoms via forcingCarrierAtomsFormula :=
  ⟨fun v ↦ by simp [forcingCarrierAtomsFormula, forcingCarrierAtoms]⟩

instance forcingCarrierPoolFormula_defined :
    ℒₛₑₜ-function₃[V] forcingCarrierPool via forcingCarrierPoolFormula :=
  ⟨fun v ↦ by simp [forcingCarrierPoolFormula, forcingCarrierPool]⟩

instance forcingCarrierNormalizeFormula_defined :
    ℒₛₑₜ-function₄[V] forcingCarrierNormalize via forcingCarrierNormalizeFormula :=
  ⟨fun v ↦ by simp [forcingCarrierNormalizeFormula, forcingCarrierNormalize]⟩

instance forcingCarrierLocalNormalizeFormula_defined :
    ℒₛₑₜ-function₅[V] forcingCarrierLocalNormalize via forcingCarrierLocalNormalizeFormula :=
  ⟨fun v ↦ by simp [forcingCarrierLocalNormalizeFormula, forcingCarrierLocalNormalize]⟩

instance forcingCarrierAtoms_definable : ℒₛₑₜ-function₃[V] forcingCarrierAtoms :=
  forcingCarrierAtomsFormula_defined.to_definable

instance forcingCarrierPool_definable : ℒₛₑₜ-function₃[V] forcingCarrierPool :=
  forcingCarrierPoolFormula_defined.to_definable

instance forcingCarrierNormalize_definable : ℒₛₑₜ-function₄[V] forcingCarrierNormalize :=
  forcingCarrierNormalizeFormula_defined.to_definable

instance forcingCarrierLocalNormalize_definable : Language.DefinableFunction₅ ℒₛₑₜ (forcingCarrierLocalNormalize (V := V)) :=
  forcingCarrierLocalNormalizeFormula_defined.to_definable

theorem forcingCarrierNormalize_isName (P R Q τ : V) :
    IsForcingName P (forcingCarrierNormalize P R Q τ) := forcingSaturatedName_isName _ _ _ _

theorem forcingCarrierLocalNormalize_isName (P R Q p τ : V) :
    IsForcingName P (forcingCarrierLocalNormalize P R Q p τ) :=
  forcingRestrictedName_isName (forcingCarrierNormalize_isName _ _ _ _)

theorem forcingCarrierNormalize_mem (P R Q τ : V) :
    forcingCarrierNormalize P R Q τ ∈ forcingCarrierPool P R Q :=
  mem_power_iff.mpr (forcingSaturatedName_subset _ _ _ _)

theorem forcingCarrierLocalNormalize_mem (P R Q p τ : V) :
    forcingCarrierLocalNormalize P R Q p τ ∈ forcingCarrierPool P R Q := by
  apply mem_power_iff.mpr
  intro z hz
  change z ∈ forcingRestrictedName P R p (forcingCarrierNormalize P R Q τ) at hz
  unfold forcingRestrictedName at hz
  obtain ⟨σ, hσ, r, hr, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact kpair_mem_iff.mpr
    ⟨forcingSaturatedName_domain_subset P R (forcingCarrierAtoms P R Q) τ _ hσ, hr⟩

theorem forcingCarrierPool_empty (P R Q : V) : (∅ : V) ∈ forcingCarrierPool P R Q := by
  exact mem_power_iff.mpr (empty_subset _)

theorem forcingCarrierPool_union {P R Q B : V} (hB : B ⊆ forcingCarrierPool P R Q) :
    ⋃ˢ B ∈ forcingCarrierPool P R Q := by
  apply mem_power_iff.mpr
  intro z hz
  obtain ⟨τ, hτ, hz⟩ := mem_sUnion_iff.mp hz
  exact (mem_power_iff.mp (hB _ hτ)) _ hz

namespace ForcingContext
variable (A : ForcingContext V)

theorem unionName_value (Q : ForcingName A.P) :
    A.ofName (forcingUnion A.R Q) = ⋃ˢ (A.ofName Q) := by
  apply mem_ext
  intro x
  have he : x ∈ A.ofName (forcingUnion A.R Q) ↔ ∃ y : A.Model, y ∈ A.ofName Q ∧ x ∈ y :=
    forcingQuotient_unionName A.P A.R A.G A.order A.generic Q x
  exact he.trans (mem_sUnion_iff (V := A.Model)).symm

theorem carrierNormalize_value (Q τ : ForcingName A.P) (hτ : A.ofName τ ∈ A.ofName Q) :
    A.ofName ⟨forcingCarrierNormalize A.P A.R Q.val τ.val, forcingCarrierNormalize_isName _ _ _ _⟩ =
      A.ofName τ := by
  apply A.saturatedName_value
  intro x hx
  have hxU : x ∈ A.ofName (forcingUnion A.R Q) := by
    rw [A.unionName_value Q]
    exact mem_sUnion_iff.mpr ⟨A.ofName τ, hτ, hx⟩
  obtain ⟨σ, p, _, hσp, he⟩ := (A.mem_ofName_iff (forcingUnion A.R Q) x).mp hxU
  exact ⟨σ, mem_domain_of_kpair_mem hσp, he⟩

theorem carrierLocalNormalize_value (Q τ : ForcingName A.P) {p : V} (hp : p ∈ A.G)
    (hτ : A.ofName τ ∈ A.ofName Q) :
    A.ofName ⟨forcingCarrierLocalNormalize A.P A.R Q.val p τ.val,
      forcingCarrierLocalNormalize_isName _ _ _ _ _⟩ = A.ofName τ :=
  (A.restrictedName_value hp
    ⟨forcingCarrierNormalize A.P A.R Q.val τ.val, forcingCarrierNormalize_isName _ _ _ _⟩).trans
      (A.carrierNormalize_value Q τ hτ)

theorem carrierSaturatedName_value (Q : ForcingName A.P) :
    A.ofName ⟨forcingSaturatedName A.P A.R (forcingCarrierPool A.P A.R Q.val) Q.val,
      forcingSaturatedName_isName _ _ _ _⟩ = A.ofName Q := by
  apply A.saturatedName_value
  intro x hx
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  exact ⟨⟨forcingCarrierNormalize A.P A.R Q.val τ.val, forcingCarrierNormalize_isName _ _ _ _⟩,
    forcingCarrierNormalize_mem _ _ _ _, (A.carrierNormalize_value Q τ hx).symm⟩

end ForcingContext

theorem forcingCarrierNormalize_forces_countable [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (Q τ : ForcingName P) (hm : p ∈ atomicMembership P R τ.val Q.val) :
    p ∈ atomicEquality P R (forcingCarrierNormalize P R Q.val τ.val) τ.val := by
  apply atomicEquality_of_all_generics hR ht hp
    ⟨forcingCarrierNormalize P R Q.val τ.val, forcingCarrierNormalize_isName _ _ _ _⟩ τ
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply A.carrierNormalize_value Q τ
  exact (forcingQuotientMk_mem_iff P R G hR hG.1 τ Q).mpr ⟨p, hpG, hm⟩

theorem eval_forcingCarrierNormalizeCorrectFormula (v : Fin 6 → V) :
    forcingCarrierNormalizeCorrectFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) → v 5 ∈ v 0 →
        v 5 ∈ atomicMembership (v 0) (v 1) (v 4) (v 3) →
        v 5 ∈ atomicEquality (v 0) (v 1)
          (forcingCarrierNormalize (v 0) (v 1) (v 3) (v 4)) (v 4)) := by
  simp [forcingCarrierNormalizeCorrectFormula]

private theorem forcingCarrierNormalizeCorrect_valid (v : Fin 6 → V) :
    forcingCarrierNormalizeCorrectFormula.Evalb v := by
  apply eval_of_countable_zf forcingCarrierNormalizeCorrectFormula
  intro W _ _ _ _ w
  apply (eval_forcingCarrierNormalizeCorrectFormula w).mpr
  intro hR ht hQ hτ hp hm
  exact forcingCarrierNormalize_forces_countable hR ht hp ⟨w 3, hQ⟩ ⟨w 4, hτ⟩ hm

theorem forcingCarrierNormalize_forces {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (Q τ : ForcingName P) (hm : p ∈ atomicMembership P R τ.val Q.val) :
    p ∈ atomicEquality P R (forcingCarrierNormalize P R Q.val τ.val) τ.val :=
  (eval_forcingCarrierNormalizeCorrectFormula ![P, R, one, Q.val, τ.val, p]).mp
    (forcingCarrierNormalizeCorrect_valid _) hR ht Q.property τ.property hp hm

theorem forcingCarrierLocalNormalize_forces_below {P R one p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q τ : ForcingName P) (hm : q ∈ atomicMembership P R τ.val Q.val) :
    q ∈ atomicEquality P R (forcingCarrierLocalNormalize P R Q.val p τ.val) τ.val :=
  atomicEquality_trans hR _ _ _ q
    (atomicEquality_mono hR (forcingRestrictedName_forces hR hp _) hq hqp)
    (forcingCarrierNormalize_forces hR ht hq Q τ hm)

theorem forcingCarrierLocalNormalize_empty {P R Q p τ : V}
    (hR : IsForcingPreorder P R) (he : p ∈ atomicEquality P R τ ∅) :
    forcingCarrierLocalNormalize P R Q p τ = ∅ :=
  forcingRestrictedSaturatedName_empty hR he

theorem carrierSaturated_twoStep_localNormalize {P R one p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q τ : ForcingName P) (hm : q ∈ atomicMembership P R τ.val Q.val) :
    ⟨q, forcingCarrierLocalNormalize P R Q.val p τ.val⟩ₖ ∈
      twoStepConditions P R (forcingSaturatedName P R (forcingCarrierPool P R Q.val) Q.val) ∅ := by
  have hn := forcingCarrierLocalNormalize_mem P R Q.val p τ.val
  have hname := forcingCarrierLocalNormalize_isName P R Q.val p τ.val
  have he := forcingCarrierLocalNormalize_forces_below hR ht hp hq hqp Q τ hm
  have hmem := ((atomicEquality_membership_iff hR he Q.val).1).mpr hm
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hq,
    mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hn hq hname hmem)),
    forcingSaturatedName_forces_member hR hn hq hname hmem⟩

end ZFVP
