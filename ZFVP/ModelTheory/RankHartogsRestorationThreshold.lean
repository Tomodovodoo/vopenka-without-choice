import ZFVP.ModelTheory.RankHartogsRestorationForcingCountable
import ZFVP.ModelTheory.HartogsRestorationForcingAgreement
import ZFVP.SetTheory.BoundedDomainParameters

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def hartogsRestorationRankThresholdFormula : SetTheorySemisentence 6 :=
  f“P R o κ γ η. γ ∈ η ∧ ∀ ξ, η ∈ ξ → !choicelessInaccessibleFormula ξ →
    ∀ U, U = !hierarchyFormula ξ → P ∈ U → R ∈ U → o ∈ U → κ ∈ U → γ ∈ U →
    ∀ p ∈ P,
      (!(boundedDomainParametersFormula (hartogsBinaryForcingFormula woodinLocalRestorationFormula)) U P R o p κ γ ↔
        !(hartogsBinaryForcingFormula woodinLocalRestorationFormula) P R o p κ γ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsHartogsRestorationRankThreshold (P R one κ γ η : V) : Prop :=
  γ ∈ η ∧ ∀ ξ, η ∈ ξ → IsChoicelessInaccessible ξ →
    ∀ U, U = hierarchy ξ → P ∈ U → R ∈ U → one ∈ U → κ ∈ U → γ ∈ U →
    ∀ p ∈ P,
      ((boundedDomainParametersFormula (hartogsBinaryForcingFormula woodinLocalRestorationFormula)).Evalb
        ![U, P, R, one, p, κ, γ] ↔
      p ∈ forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]))

private theorem forall_six_eq {W : Type*} (a b c d e f : W)
    (F : W → W → W → W → W → W → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_seven_eq {W : Type*} (a b c d e f g : W)
    (F : W → W → W → W → W → W → W → Prop) :
    (∀ t u v w x y z, t = a → u = b → v = c → w = d → x = e → y = f → z = g → F t u v w x y z) ↔ F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h t u v w x y z ht hu hv hw hx hy hz ↦ by subst t u v w x y z; exact h⟩

instance hartogsRestorationRankThresholdFormula_defined :
    Defined (fun v : Fin 6 → V ↦ IsHartogsRestorationRankThreshold (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
      hartogsRestorationRankThresholdFormula :=
  ⟨fun v ↦ by simp [hartogsRestorationRankThresholdFormula, IsHartogsRestorationRankThreshold,
    Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ,
    forall_six_eq, forall_seven_eq]⟩

instance hartogsRestorationRankThreshold_definable : Language.DefinableRel₆ ℒₛₑₜ
    (IsHartogsRestorationRankThreshold (V := V)) :=
  hartogsRestorationRankThresholdFormula_defined.to_definable

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_domain_hartogsBinaryForcing (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R one p κ γ : SetDomain U) :
    (boundedDomainParametersFormula (hartogsBinaryForcingFormula woodinLocalRestorationFormula)).Evalb
      ![U, P.val, R.val, one.val, p.val, κ.val, γ.val] ↔
      p ∈ forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]) := by
  have hv : (fun i : Fin 6 ↦ ((![P, R, one, p, κ, γ] : Fin 6 → SetDomain U) i).val) =
      ![P.val, R.val, one.val, p.val, κ.val, γ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.cases rfl
        (fun z ↦ Fin.elim0 z) n) m) l) k) j) i
  have he := eval_boundedDomainParametersFormula
    (hartogsBinaryForcingFormula woodinLocalRestorationFormula) U ![P, R, one, p, κ, γ]
  rw [hv] at he
  exact he.trans (Defined.eval_iff (φ := hartogsBinaryForcingFormula woodinLocalRestorationFormula)
    ![P, R, one, p, κ, γ])

theorem hartogsRestorationRankThreshold_exists_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκγ : κ ∈ γ) (hγδ : γ ∈ δ)
    (hγ : IsChoicelessInaccessible γ) (hPγ : P ∈ hierarchy γ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ β ∈ δ, IsHartogsRestorationRankThreshold P R one κ γ β := by
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_rank_hartogsRestoration_forcing_eq_countable
    hδ hP hκγ hγδ hγ hPγ hR ht hκ
  refine ⟨β, hβ, hγβ, ?_⟩
  intro ξ hβξ hξ U hU hPU hRU hoU hkU hgU x hxP
  subst U
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let p : SetDomain (hierarchy ξ) := ⟨P, hPU⟩
  let r : SetDomain (hierarchy ξ) := ⟨R, hRU⟩
  let o : SetDomain (hierarchy ξ) := ⟨one, hoU⟩
  let k : SetDomain (hierarchy ξ) := ⟨κ, hkU⟩
  let d : SetDomain (hierarchy ξ) := ⟨γ, hgU⟩
  let z : SetDomain (hierarchy ξ) := ⟨x, (hierarchy_transitive ξ).mem_trans hxP hPU⟩
  have he := hall ξ hβξ hξ p r o k d rfl rfl rfl rfl rfl
  apply (eval_domain_hartogsBinaryForcing (hierarchy ξ) p r o z k d).trans
  change x ∈ (forcingFormula p r woodinLocalRestorationFormula
    (standardTuple ![hartogsNumberName p r (checkName o k), checkName o d])).val ↔ _
  rw [he]

def existsHartogsRestorationRankThresholdFormula : SetTheorySemisentence 6 :=
  f“δ κ γ P R o. !woodinSupercompactFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ∈ γ ∧ γ ∈ δ ∧
    !choicelessInaccessibleFormula γ ∧ P ∈ !hierarchyFormula γ ∧
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    (∀ p ∈ P, !(namedUnaryForcingFormula regularCardinalFormula) P R p
      (!hartogsNumberNameFormula P R (!checkNameFormula o κ))) →
    ∃ β ∈ δ, !hartogsRestorationRankThresholdFormula P R o κ γ β”

private theorem forall_three_eq {W : Type*} (a b c : W) (F : W → W → W → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_four_eq {W : Type*} (a b c d : W) (F : W → W → W → W → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → F u v w x) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, fun h u v w x hu hv hw hx ↦ by subst u v w x; exact h⟩

theorem eval_existsHartogsRestorationRankThresholdFormula (v : Fin 6 → V) :
    existsHartogsRestorationRankThresholdFormula.Evalb v ↔
      (IsWoodinSupercompact (v 0) → v 3 ∈ hierarchy (v 0) → v 1 ∈ v 2 → v 2 ∈ v 0 →
        IsChoicelessInaccessible (v 2) → v 3 ∈ hierarchy (v 2) →
        IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
        (∀ p ∈ v 3, p ∈ forcingFormula (v 3) (v 4) regularCardinalFormula
          (standardTuple ![hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 1))])) →
        ∃ β ∈ v 0, IsHartogsRestorationRankThreshold (v 3) (v 4) (v 5) (v 1) (v 2) β) := by
  simp [existsHartogsRestorationRankThresholdFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq, forall_three_eq, forall_four_eq]

theorem hartogsRestorationRankThreshold_exists
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκγ : κ ∈ γ) (hγδ : γ ∈ δ)
    (hγ : IsChoicelessInaccessible γ) (hPγ : P ∈ hierarchy γ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ β ∈ δ, IsHartogsRestorationRankThreshold P R one κ γ β := by
  have he := eval_of_countable_zf existsHartogsRestorationRankThresholdFormula (by
    intro W _ _ _ _ v
    apply (eval_existsHartogsRestorationRankThresholdFormula v).mpr
    intro hδ hP hκγ hγδ hγ hPγ hR ht hκ
    exact hartogsRestorationRankThreshold_exists_countable hδ hP hκγ hγδ hγ hPγ hR ht hκ)
    ![δ, κ, γ, P, R, one]
  exact (eval_existsHartogsRestorationRankThresholdFormula _).mp he hδ hP hκγ hγδ hγ hPγ hR ht hκ

theorem IsHartogsRestorationRankThreshold.mono {P R one κ γ η β : V} [IsOrdinal β]
    (h : IsHartogsRestorationRankThreshold P R one κ γ η) (hηβ : η ∈ β) :
    IsHartogsRestorationRankThreshold P R one κ γ β := by
  refine ⟨IsOrdinal.toIsTransitive.mem_trans h.1 hηβ, ?_⟩
  intro ξ hβξ hξ
  let := hξ.1
  exact h.2 ξ (IsOrdinal.toIsTransitive.mem_trans hηβ hβξ) hξ

theorem IsHartogsRestorationRankThreshold.rank_cutoff_iff {ξ β : V}
    (hξ : IsChoicelessInaccessible ξ) (hβξ : β ∈ ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ P R one κ γ : SetDomain (hierarchy ξ),
      IsHartogsRestorationRankThreshold P.val R.val one.val κ.val γ.val β →
      (IsWoodinNamedPrefixCutoff P R one κ (hartogsNumberName P R (checkName one κ)) γ ↔
        IsWoodinNamedPrefixCutoff P.val R.val one.val κ.val
          (hartogsNumberName P.val R.val (checkName one.val κ.val)) γ.val) := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro P R one κ γ h
  unfold IsWoodinNamedPrefixCutoff
  apply and_congr Iff.rfl
  apply and_congr (rank_choicelessInaccessible_iff
    (fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb) γ)
  have he (p : SetDomain (hierarchy ξ)) (hp : p ∈ P) :
      p ∈ forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]) ↔
      p.val ∈ forcingFormula P.val R.val woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName P.val R.val (checkName one.val κ.val), checkName one.val γ.val]) :=
    (eval_domain_hartogsBinaryForcing (hierarchy ξ) P R one p κ γ).symm.trans
      (h.2 ξ hβξ hξ (hierarchy ξ) rfl P.property R.property one.property κ.property γ.property p.val hp)
  constructor
  · intro hf p hp
    let p' : SetDomain (hierarchy ξ) := ⟨p, (hierarchy_transitive ξ).mem_trans hp P.property⟩
    exact (he p' hp).mp (hf p' hp)
  · intro hf p hp
    exact (he p hp).mpr (hf p.val hp)

theorem IsWoodinSupercompact.bounded_hartogsRestorationRankThreshold {δ κ θ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hθδ : θ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ η ∈ δ, ∀ γ ∈ θ, κ ∈ γ → IsChoicelessInaccessible γ → P ∈ hierarchy γ →
      IsHartogsRestorationRankThreshold P R one κ γ η := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hθδ
  let T : V → V → Prop := fun γ η ↦ IsOrdinal η ∧
    (κ ∈ γ → IsChoicelessInaccessible γ → P ∈ hierarchy γ →
      IsHartogsRestorationRankThreshold P R one κ γ η)
  have hcut : ℒₛₑₜ-relation (fun γ η ↦ IsHartogsRestorationRankThreshold P R one κ γ η) := by
    apply Language.Definable.substitution hartogsRestorationRankThreshold_definable
      (f := fun i v ↦ (![P, R, one, κ, v 0, v 1] : Fin 6 → V) i)
    intro i
    exact Fin.cases (by definability) (fun j ↦ Fin.cases (by definability)
      (fun k ↦ Fin.cases (by definability) (fun l ↦ Fin.cases (by definability)
        (fun m ↦ Fin.cases (by definability) (fun n ↦ Fin.cases (by definability)
          (fun z ↦ Fin.elim0 z) n) m) l) k) j) i
  have hgood : ℒₛₑₜ-predicate (fun γ : V ↦ κ ∈ γ ∧ IsChoicelessInaccessible γ ∧ P ∈ hierarchy γ) := by
    definability
  have hT' : ℒₛₑₜ-relation (fun γ η ↦ IsOrdinal η ∧
      ((κ ∈ γ ∧ IsChoicelessInaccessible γ ∧ P ∈ hierarchy γ) →
        IsHartogsRestorationRankThreshold P R one κ γ η)) := by definability
  have hT : ℒₛₑₜ-relation T := by
    apply Language.Definable.of_iff hT'
    intro v
    simp only [T, and_imp]
  have hex : ∀ γ ∈ θ, ∃ η ∈ hierarchy δ, T γ η := by
    intro γ hγ
    by_cases h : κ ∈ γ ∧ IsChoicelessInaccessible γ ∧ P ∈ hierarchy γ
    · obtain ⟨η, hη, hηT⟩ := hartogsRestorationRankThreshold_exists hδ hP h.1
        (IsOrdinal.toIsTransitive.mem_trans hγ hθδ) h.2.1 h.2.2 hR ht hκ
      let := IsOrdinal.of_mem hη
      exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, fun _ _ _ ↦ hηT⟩
    · exact ⟨∅, ordinal_mem_hierarchy_iff.mpr (hδ.inaccessible.regular.2.1 ∅ (by simp)),
        inferInstance, fun hk hg hp ↦ False.elim (h ⟨hk, hg, hp⟩)⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hθδ) T hT hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro γ hγ hk hg hp
  obtain ⟨η, hηb, hηord, hηT⟩ := hall γ hγ
  let := hηord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact (hηT hk hg hp).mono hη

end ZFVP

