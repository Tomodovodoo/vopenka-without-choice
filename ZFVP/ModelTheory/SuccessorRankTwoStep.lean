import ZFVP.ModelTheory.ForcingRankFormulaNames
import ZFVP.SetTheory.CnSequenceNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneTwoStepNamesFormula : SetTheorySemisentence 4 :=
  “N P Q t. ∀ z, z ∈ N ↔ z = t ∨ ∃ p ∈ P, ∃ a ∈ Q, !boundedKpairFormula a z p”

theorem piOneTwoStepNamesFormula_piOne : IsPiFormula 1 piOneTwoStepNamesFormula :=
  .all (.bounded ((IsBoundedSetFormula.rel _ _).iff (.or (.rel _ _)
    (.exs (.bvar 2) (.exs (.bvar 4) (boundedKpairFormula_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piOneTwoStepNamesFormula {P Q : V} (hQ : IsForcingName P Q) (N t : V) :
    piOneTwoStepNamesFormula.Evalb ![N, P, Q, t] ↔ N = twoStepNames Q t := by
  have hh : piOneTwoStepNamesFormula.Evalb ![N, P, Q, t] ↔
      ∀ z : V, z ∈ N ↔ z = t ∨ ∃ p ∈ P, ⟨z, p⟩ₖ ∈ Q := by simp [piOneTwoStepNamesFormula]
  have hm (z : V) : z = t ∨ (∃ p ∈ P, ⟨z, p⟩ₖ ∈ Q) ↔ z ∈ twoStepNames Q t := by
    change _ ↔ z ∈ domain Q ∪ {t}
    rw [mem_union_iff, mem_singleton_iff, mem_domain_iff]
    constructor
    · rintro (h | ⟨p, _, hp⟩)
      · exact Or.inr h
      · exact Or.inl ⟨p, hp⟩
    · rintro (⟨p, hp⟩ | h)
      · exact Or.inr ⟨p, forcingName_condition hQ hp, hp⟩
      · exact Or.inl h
  rw [hh, mem_ext_iff]
  exact forall_congr' (fun z ↦ iff_congr Iff.rfl (hm z))

theorem twoStepNames_mem_hierarchy {ρ Q t : V} (hρ : Cn 1 ρ)
    (hQ : Q ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ) : twoStepNames Q t ∈ hierarchy ρ := by
  let := hρ.ordinal
  exact hρ.union_closed (hρ.domain_closed hQ)
    (by simpa using pair_mem_hierarchy_limit hρ.successor_closed ht ht)

theorem twoStepConditions_mem_hierarchy {ρ P R Q t : V} (hρ : Cn 1 ρ)
    (hP : P ∈ hierarchy ρ) (hQ : Q ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ) :
    twoStepConditions P R Q t ∈ hierarchy ρ := by
  let := hρ.ordinal
  exact subset_mem_hierarchy_limit hρ.successor_closed
    (prod_mem_hierarchy_limit hρ.successor_closed hP (twoStepNames_mem_hierarchy hρ hQ ht)) sep_subset

theorem twoStepOrder_mem_hierarchy {ρ P R Q S t : V} (hρ : Cn 1 ρ)
    (hP : P ∈ hierarchy ρ) (hQ : Q ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ) :
    twoStepOrder P R Q S t ∈ hierarchy ρ := by
  let := hρ.ordinal
  have hC := twoStepConditions_mem_hierarchy (R := R) hρ hP hQ ht
  exact subset_mem_hierarchy_limit hρ.successor_closed
    (prod_mem_hierarchy_limit hρ.successor_closed hC hC) sep_subset

theorem successorRankEmbedding_value_twoStepNames {ρ γ e P Q t : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hQ : Q ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ)
    (hn : IsForcingName P Q) : e ‘ (twoStepNames Q t) = twoStepNames (e ‘ Q) (e ‘ t) := by
  have hh := successorRankEmbedding_pi_iff hρ hγ he piOneTwoStepNamesFormula_piOne
    ![twoStepNames Q t, P, Q, t] (by simp [Fin.forall_fin_iff_zero_and_forall_succ,
      twoStepNames_mem_hierarchy hρ hQ ht, hP, hQ, ht])
  have hv : (fun i ↦ e ‘ (![twoStepNames Q t, P, Q, t] i)) =
      ![e ‘ (twoStepNames Q t), e ‘ P, e ‘ Q, e ‘ t] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  rw [hv] at hh
  exact (eval_piOneTwoStepNamesFormula
    ((successorRankEmbedding_forcingName_iff hρ hγ he hP hQ).mp hn) _ _).mp
    (hh.mp ((eval_piOneTwoStepNamesFormula hn _ _).mpr rfl))

def sigmaOneTwoStepConditionFormula : SetTheorySemisentence 4 :=
  “z P R Q. ∃ p, ∃ τ, !boundedKpairFormula z p τ ∧
    !(sigmaOneAtomicMembershipFormula true) P R τ Q p”

theorem sigmaOneTwoStepConditionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepConditionFormula :=
  .exs (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    ((sigmaOneAtomicMembershipFormula_sigmaOne true).subst _)))

theorem twoStepConditions_separation (P R Q t z : V) :
    z ∈ twoStepConditions P R Q t ↔ z ∈ P ×ˢ twoStepNames Q t ∧
      sigmaOneTwoStepConditionFormula.Evalb ![z, P, R, Q] := by
  have hh : sigmaOneTwoStepConditionFormula.Evalb ![z, P, R, Q] ↔
      ∃ p τ : V, z = ⟨p, τ⟩ₖ ∧ p ∈ atomicMembership P R τ Q := by
    simp [sigmaOneTwoStepConditionFormula, TruthAnswer]
  rw [hh]
  constructor
  · intro hz
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
    exact ⟨kpair_mem_iff.mpr ⟨hp, hτ⟩, p, τ, rfl, hm⟩
  · rintro ⟨hz, p, τ, rfl, hm⟩
    exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr
      ⟨(kpair_mem_iff.mp hz).1, (kpair_mem_iff.mp hz).2, hm⟩

theorem successorRankEmbedding_value_twoStepConditions {ρ γ e P R Q t : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hQ : Q ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ)
    (hn : IsForcingName P Q) :
    e ‘ (twoStepConditions P R Q t) = twoStepConditions (e ‘ P) (e ‘ R) (e ‘ Q) (e ‘ t) := by
  let := hρ.ordinal
  have hN := twoStepNames_mem_hierarchy hρ hQ ht
  have hs := successorRankEmbedding_separation hρ hγ he sigmaOneTwoStepConditionFormula_sigmaOne
    ![P, R, Q] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hR, hQ])
    (twoStepConditions_mem_hierarchy hρ hP hQ ht)
    (prod_mem_hierarchy_limit hρ.successor_closed hP hN) (twoStepConditions_separation P R Q t)
  have hv : (fun i ↦ e ‘ (![P, R, Q] i)) = ![e ‘ P, e ‘ R, e ‘ Q] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv, successorRankEmbedding_value_product hρ hγ he hP hN,
    successorRankEmbedding_value_twoStepNames hρ hγ he hP hQ ht hn] at hs
  apply mem_ext
  intro z
  exact (hs z).trans (twoStepConditions_separation _ _ _ _ _).symm

def twoStepOrderPredicate (θ : SetTheorySemisentence 8) : SetTheorySemisentence 6 :=
  “z P R S Γ F. ∃ p, ∃ q, ∃ σ, ∃ τ, ∃ a, ∃ b,
    !boundedKpairFormula a p σ ∧ !boundedKpairFormula b q τ ∧
    !boundedKpairFormula z a b ∧ !boundedPairMemberFormula R p q ∧ !θ P R Γ F p S σ τ”

theorem twoStepOrderPredicate_sigmaOne {θ : SetTheorySemisentence 8} (hθ : IsSigmaFormula 1 θ) :
    IsSigmaFormula 1 (twoStepOrderPredicate θ) :=
  .exs (.exs (.exs (.exs (.exs (.exs
    (.and (.bounded (boundedKpairFormula_bounded.subst _))
      (.and (.bounded (boundedKpairFormula_bounded.subst _))
        (.and (.bounded (boundedKpairFormula_bounded.subst _))
          (.and (.bounded (boundedPairMemberFormula_bounded.subst _)) (hθ.subst _))))))))))

theorem eval_twoStepOrderPredicate (θ : SetTheorySemisentence 8) (z P R S Γ F : V) :
    (twoStepOrderPredicate θ).Evalb ![z, P, R, S, Γ, F] ↔
      ∃ p q σ τ : V, z = ⟨⟨p, σ⟩ₖ, ⟨q, τ⟩ₖ⟩ₖ ∧ ⟨p, q⟩ₖ ∈ R ∧
        θ.Evalb ![P, R, Γ, F, p, S, σ, τ] := by
  simp [twoStepOrderPredicate, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem twoStepOrder_separation {P R Q S t : V} (hR : IsForcingPreorder P R)
    (h : IsForcingIterand P R Q S t) {θ : SetTheorySemisentence 8}
    (hm : IsForcingTranslation (V := V) false boundedPairMemberFormula θ) (z : V) :
    z ∈ twoStepOrder P R Q S t ↔
      z ∈ twoStepConditions P R Q t ×ˢ twoStepConditions P R Q t ∧
        (twoStepOrderPredicate θ).Evalb ![z, P, R, S, ∅, ∅] := by
  rw [eval_twoStepOrderPredicate]
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    obtain ⟨p, hp, σ, hσ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    obtain ⟨q, hq, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
    have hv := (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hz
    have hf : p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, σ, τ]) := by
      simpa using hv.2.2.2
    exact ⟨kpair_mem_iff.mpr ⟨ha, hb⟩, p, q, σ, τ, rfl, by simpa using hv.2.2.1,
      (hm P R ∅ ∅ hR (by simp) ![S, σ, τ]
        (fun i ↦ Fin.cases h.orderName (fun j ↦ Fin.cases (h.name hσ) (fun k ↦ Fin.cases (h.name hτ) (fun l ↦ Fin.elim0 l) k) j) i) p).mpr hf⟩
  · rintro ⟨hz, p, q, σ, τ, rfl, hpq, hθ⟩
    obtain ⟨ha, hb⟩ := kpair_mem_iff.mp hz
    have hσ := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp ha).2.1
    have hτ := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hb).2.1
    apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨ha, hb, by simpa using hpq, ?_⟩
    have hf : p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, σ, τ]) := (hm P R ∅ ∅ hR (by simp) ![S, σ, τ]
      (fun i ↦ Fin.cases h.orderName (fun j ↦ Fin.cases (h.name hσ) (fun k ↦ Fin.cases (h.name hτ) (fun l ↦ Fin.elim0 l) k) j) i) p).mp hθ
    simpa using hf

theorem successorRankEmbedding_value_twoStepOrder {ρ γ e P R Q S t : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hQ : Q ∈ hierarchy ρ)
    (hS : S ∈ hierarchy ρ) (ht : t ∈ hierarchy ρ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    (h : IsForcingIterand P R Q S t)
    (h' : IsForcingIterand (e ‘ P) (e ‘ R) (e ‘ Q) (e ‘ S) (e ‘ t)) :
    e ‘ (twoStepOrder P R Q S t) = twoStepOrder (e ‘ P) (e ‘ R) (e ‘ Q) (e ‘ S) (e ‘ t) := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have h0 : (∅ : V) ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hρ.omega_lt)
  have he0 : e ‘ (∅ : V) = ∅ := he.value_empty
    (hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ h0)
  have hC := twoStepConditions_mem_hierarchy (R := R) hρ hP hQ ht
  have hφ : IsSigmaFormula 1 boundedPairMemberFormula := .bounded boundedPairMemberFormula_bounded
  obtain ⟨θ, hθ, hm⟩ := hφ.forcing_translation (V := V) false (by decide)
  have hs := successorRankEmbedding_separation hρ hγ he (twoStepOrderPredicate_sigmaOne hθ)
    ![P, R, S, ∅, ∅]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hR, hS, h0])
    (twoStepOrder_mem_hierarchy hρ hP hQ ht)
    (prod_mem_hierarchy_limit hρ.successor_closed hC hC) (twoStepOrder_separation hord h hm)
  have hv : (fun i ↦ e ‘ (![P, R, S, ∅, ∅] i)) = ![e ‘ P, e ‘ R, e ‘ S, ∅, ∅] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases he0 (fun m ↦ Fin.cases he0 (fun n ↦ Fin.elim0 n) m) l) k) j) i
  rw [hv, successorRankEmbedding_value_product hρ hγ he hC hC,
    successorRankEmbedding_value_twoStepConditions hρ hγ he hP hR hQ ht h.posetName] at hs
  apply mem_ext
  intro z
  exact (hs z).trans (twoStepOrder_separation hord' h' hm z).symm

end ZFVP

