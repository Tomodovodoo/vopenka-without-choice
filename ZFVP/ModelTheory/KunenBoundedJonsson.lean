import ZFVP.ModelTheory.KunenUnconditional
import ZFVP.ModelTheory.LimitRankEmbeddingAction
import ZFVP.ModelTheory.EmbeddingSetOperations

/-! A bounded formula for the omega-Jonsson predicate, and Kunen's contradiction off `C(1)`.

`ZFVP.ModelTheory.KunenCnTwo` transfers the omega-Jonsson predicate along a coded self-embedding
through its Pi-two form, so the stage there has to be in `C(2)`. Once the rank stage
`hierarchy (succ (succ (succ lam)))` is handed to the formula as a third argument, every quantifier
in the predicate can be bounded by it: the subsets of `lam` and the injections witnessing
`lam ≤# A` and the enumerations `g ∈ a ^ ω` all sit there. A bounded formula transfers along any
coded embedding between transitive sets, so the whole argument runs with the stage only in `C(1)`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The omega-Jonsson predicate with every quantifier bounded by a third argument `W`, meant to be
a rank stage above `l`. -/
def boundedOmegaJonssonFormula : SetTheorySemisentence 3 :=
  “F l W. !boundedIsFunctionFormula F ∧ !omegaJonssonDomainConditionFormula F l ∧
    ∀ A ∈ W, ∀ i ∈ W, (A ⊆ l ∧ !boundedInjectionFormula i l A) → ∀ c ∈ l,
      ∃ a ∈ W, !boundedMemDomainFormula a F ∧ a ⊆ A ∧
        (∃ g ∈ W, ∃ w ∈ W, !boundedOmegaFormula w ∧ !boundedFunctionFormula g w a ∧
          ∀ y ∈ a, ∃ n ∈ w, !boundedPairMemberFormula g n y) ∧
        !boundedPairMemberFormula F a c”

theorem boundedOmegaJonssonFormula_bounded : IsBoundedSetFormula boundedOmegaJonssonFormula :=
  .and (boundedIsFunctionFormula_bounded.subst _)
    (.and (omegaJonssonDomainConditionFormula_bounded.subst _)
      (.all (.bvar 2) (.all (.bvar 3)
        (.or (IsBoundedSetFormula.and (isSubsetOf_bounded.subst _)
            (boundedInjectionFormula_bounded.subst _)).neg
          (.all (.bvar 3) (.exs (.bvar 5)
            (.and (boundedMemDomainFormula_bounded.subst _)
              (.and (isSubsetOf_bounded.subst _)
                (.and
                  (.exs (.bvar 6) (.exs (.bvar 7)
                    (.and (boundedOmegaFormula_bounded.subst _)
                      (.and (boundedFunctionFormula_bounded.subst _)
                        (.all (.bvar 2) (.exs (.bvar 1)
                          (boundedPairMemberFormula_bounded.subst _)))))))
                  (boundedPairMemberFormula_bounded.subst _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal reading of `boundedOmegaJonssonFormula`. -/
def BoundedOmegaJonsson (F l W : V) : Prop :=
  IsFunction F ∧ OmegaJonssonDomainCondition F l ∧
    ∀ A ∈ W, ∀ i ∈ W, (A ⊆ l ∧ (i ∈ A ^ l ∧ Injective i)) → ∀ c ∈ l,
      ∃ a ∈ W, a ∈ domain F ∧ a ⊆ A ∧
        (∃ g ∈ W, ∃ w ∈ W, w = (ω : V) ∧ g ∈ a ^ w ∧ ∀ y ∈ a, ∃ n ∈ w, ⟨n, y⟩ₖ ∈ g) ∧
        ⟨a, c⟩ₖ ∈ F

instance boundedOmegaJonssonFormula_defined :
    ℒₛₑₜ-relation₃[V] BoundedOmegaJonsson via boundedOmegaJonssonFormula :=
  ⟨fun v ↦ by simp [boundedOmegaJonssonFormula, BoundedOmegaJonsson]⟩

/-- Members of an ordinal sit in the rank stage of that ordinal. -/
private theorem mem_hierarchy_of_mem_ordinal {lam x : V} [IsOrdinal lam] (hx : x ∈ lam) :
    x ∈ hierarchy lam := by
  have : IsOrdinal x := IsOrdinal.of_mem hx
  exact ordinal_mem_hierarchy_iff.mpr hx

/-- A subset of an ordinal sits one stage up. -/
private theorem subset_mem_hierarchy_succ {lam A : V} [IsOrdinal lam] (hA : A ⊆ lam) :
    A ∈ hierarchy (succ lam) := by
  rw [hierarchy_succ, mem_power_iff]
  intro x hx
  exact mem_hierarchy_of_mem_ordinal (hA x hx)

private theorem succ_mem_succ_succ_succ {lam : V} [IsOrdinal lam] :
    succ lam ∈ succ (succ (succ lam)) :=
  mem_succ_iff.mpr (Or.inr (mem_succ_self (succ lam)))

/-- A subset of an ordinal sits in the third stage above it. -/
private theorem subset_mem_hierarchy_three {lam A : V} [IsOrdinal lam] (hA : A ⊆ lam) :
    A ∈ hierarchy (succ (succ (succ lam))) :=
  mem_hierarchy_of_mem_stage succ_mem_succ_succ_succ (subset_mem_hierarchy_succ hA)

/-- A set of Kuratowski pairs of members of an ordinal sits in the third stage above it. -/
private theorem pairs_mem_hierarchy_three {lam r : V} [IsOrdinal lam]
    (hr : ∀ p ∈ r, ∃ x ∈ lam, ∃ y ∈ lam, p = ⟨x, y⟩ₖ) :
    r ∈ hierarchy (succ (succ (succ lam))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := hr p hp
  exact kpair_mem_hierarchy_succ_succ (mem_hierarchy_of_mem_ordinal hx)
    (mem_hierarchy_of_mem_ordinal hy)

/-- An internal function between subsets of an ordinal sits in the third stage above it. -/
private theorem function_mem_hierarchy_three {lam X Y r : V} [IsOrdinal lam]
    (hX : X ⊆ lam) (hY : Y ⊆ lam) (hr : r ∈ Y ^ X) :
    r ∈ hierarchy (succ (succ (succ lam))) := by
  refine pairs_mem_hierarchy_three (fun p hp ↦ ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hr p hp)
  exact ⟨x, hX x hx, y, hY y hy, rfl⟩

/-- The bounded reading of the omega-Jonsson predicate at the stage `hierarchy (succ (succ (succ
lam)))` says exactly that `F` is omega-Jonsson for `lam`. -/
theorem boundedOmegaJonsson_iff {F lam : V} (hlamord : IsOrdinal lam) (hω : (ω : V) ⊆ lam) :
    BoundedOmegaJonsson F lam (hierarchy (succ (succ (succ lam)))) ↔ IsOmegaJonsson F lam := by
  let := hlamord
  have hωW : (ω : V) ∈ hierarchy (succ (succ (succ lam))) := subset_mem_hierarchy_three hω
  constructor
  · rintro ⟨hfun, hdom, hcl⟩
    let := hfun
    refine ⟨hfun, omegaJonssonDomainCondition_iff.mp hdom, ?_⟩
    rintro A hAsub ⟨i, hi, hinj⟩ c hc
    have hAW := subset_mem_hierarchy_three hAsub
    have hiW := function_mem_hierarchy_three (fun x hx ↦ hx) (fun y hy ↦ hAsub y hy) hi
    obtain ⟨a, -, hadom, haA, ⟨g, -, w, -, rfl, hg, hsurj⟩, hac⟩ :=
      hcl A hAW i hiW ⟨hAsub, hi, hinj⟩ c hc
    refine ⟨a, hadom, haA, ⟨g, hg, ?_⟩, value_eq_of_kpair_mem hac⟩
    apply SetTheory.subset_antisymm
    · exact range_subset_of_subset_prod (subset_prod_of_mem_function hg)
    · intro y hy
      obtain ⟨n, -, hn⟩ := hsurj y hy
      exact mem_range_of_kpair_mem hn
  · rintro ⟨hfun, hdom, hcl⟩
    let := hfun
    refine ⟨hfun, omegaJonssonDomainCondition_iff.mpr hdom, ?_⟩
    rintro A - i - ⟨hAsub, hi, hinj⟩ c hc
    obtain ⟨a, hadom, haA, ⟨g, hg, hrange⟩, hval⟩ := hcl A hAsub ⟨i, hi, hinj⟩ c hc
    have halam : a ⊆ lam := fun x hx ↦ hAsub x (haA x hx)
    refine ⟨a, subset_mem_hierarchy_three halam, hadom, haA,
      ⟨g, function_mem_hierarchy_three hω halam hg, (ω : V), hωW, rfl, hg, ?_⟩,
      hval ▸ kpair_value_mem hadom⟩
    intro y hy
    obtain ⟨n, hn⟩ := mem_range_iff.mp (hrange.symm ▸ hy)
    exact ⟨n, (kpair_mem_iff.mp (subset_prod_of_mem_function hg _ hn)).1, hn⟩

theorem eval_boundedOmegaJonssonFormula {F lam : V} (hlamord : IsOrdinal lam)
    (hω : (ω : V) ⊆ lam) :
    boundedOmegaJonssonFormula.Evalb ![F, lam, hierarchy (succ (succ (succ lam)))] ↔
      IsOmegaJonsson F lam :=
  ((boundedOmegaJonssonFormula_defined (V := V)).iff
    ![F, lam, hierarchy (succ (succ (succ lam)))]).trans (boundedOmegaJonsson_iff hlamord hω)

/-- The image of an omega-Jonsson function under a coded self-embedding of a `C(1)` rank stage is
omega-Jonsson for the image of the ordinal, provided the stage reaches past `lam` by three
successors. -/
theorem IsOmegaJonsson.value_bounded {δ f F lam : V} (hδ : Cn 1 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hF : F ∈ hierarchy δ) (hlam : lam ∈ hierarchy δ) (hlamord : IsOrdinal lam)
    (hω : (ω : V) ⊆ lam) (h2 : succ (succ lam) ∈ δ) (hJ : IsOmegaJonsson F lam) :
    IsOmegaJonsson (f ‘ F) (f ‘ lam) := by
  let := hδ.ordinal
  let := hlamord
  let := hierarchy_transitive δ
  have hsucc : ∀ β ∈ δ, succ β ∈ δ := hδ.successor_closed
  have hωδ : (ω : V) ∈ hierarchy δ := ((cn_successor_iff 0 δ).mp hδ).2.support.omega_mem
  -- the three successor stages above `lam` all lie in `δ`
  have h1δ : succ lam ∈ δ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ lam)) h2
  have h0δ : lam ∈ δ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self lam) h1δ
  have h3δ : succ (succ (succ lam)) ∈ δ := hsucc _ h2
  have h1H : succ lam ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr h1δ
  have h2H : succ (succ lam) ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr h2
  have h3H : succ (succ (succ lam)) ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr h3δ
  -- the embedding turns the stage above `lam` into the stage above `f ‘ lam`
  have hvsucc : f ‘ (succ (succ (succ lam))) = succ (succ (succ (f ‘ lam))) := by
    rw [h.value_succ h2H h3H, h.value_succ h1H h2H, h.value_succ hlam h1H]
  have hvW := (limitRankEmbedding_value_hierarchy hsucc hsucc h
    (IsOrdinal.succ (h := IsOrdinal.succ (h := IsOrdinal.succ))) h3H).2
  rw [hvsucc] at hvW
  -- the image ordinal is an ordinal above `ω`
  have hvord : IsOrdinal (f ‘ lam) :=
    (limitRankEmbedding_value_hierarchy hsucc hsucc h hlamord hlam).1
  have hvω : (ω : V) ⊆ f ‘ lam := by
    have := h.value_subset hωδ hlam hω
    rwa [h.value_omega hωδ] at this
  -- a bounded formula transfers along the embedding
  have hv : ∀ i, (![F, lam, hierarchy (succ (succ (succ lam)))] : Fin 3 → V) i ∈ hierarchy δ := by
    intro i
    refine Fin.cases hF (fun j ↦ Fin.cases hlam (fun t ↦ Fin.cases ?_ (fun s ↦ Fin.elim0 s) t) j) i
    exact hierarchy_mem h3δ
  have hiff := h.bounded_defined_iff boundedOmegaJonssonFormula_bounded
    (fun v ↦ BoundedOmegaJonsson (v 0) (v 1) (v 2))
    ![F, lam, hierarchy (succ (succ (succ lam)))] hv
  have himg := hiff.mp ((boundedOmegaJonsson_iff hlamord hω).mpr hJ)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at himg
  rw [show (![F, lam, hierarchy (succ (succ (succ lam)))] : Fin 3 → V) 2 =
    hierarchy (succ (succ (succ lam))) from rfl, hvW] at himg
  exact (boundedOmegaJonsson_iff hvord hvω).mp himg

/-- Enlarging the codomain of an internal function. -/
private theorem mem_function_mono' {g X Y Y' : V} (hg : g ∈ Y ^ X) (hY : Y ⊆ Y') : g ∈ Y' ^ X := by
  refine mem_function_iff.mpr ⟨fun p hp ↦ ?_, (mem_function_iff.mp hg).2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 p hp)
  exact kpair_mem_iff.mpr ⟨hx, hY y hy⟩

/-- Kunen's contradiction at a `C(1)` rank stage: a coded self-embedding whose critical limit plus
two successors sits inside the stage rules out an omega-Jonsson function for that limit inside the
stage. -/
theorem false_of_omegaJonsson_criticalLimit_bounded {δ f κ F : V} (hδ : Cn 1 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hlim2 : succ (succ (criticalLimit f κ)) ∈ δ)
    (hF : F ∈ hierarchy δ) (hJ : IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  set lam : V := criticalLimit f κ with hlamdef
  have hω : (ω : V) ∈ hierarchy δ := ((cn_successor_iff 0 δ).mp hδ).2.support.omega_mem
  have hlamord : IsOrdinal lam := CriticalSequence.limit_ordinal hδ h hκ
  let := hlamord
  have hlamδ : lam ∈ δ :=
    IsOrdinal.toIsTransitive.mem_trans (mem_succ_self lam)
      (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ lam)) hlim2)
  have hlim : lam ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hlamδ
  have hωlam : (ω : V) ⊆ lam :=
    IsOrdinal.toIsTransitive.transitive _ (CriticalSequence.omega_mem_limit hδ h hκ)
  have hfix : f ‘ lam = lam := CriticalSequence.limit_fixed hδ h hκ hlim
  have hκlam : κ ∈ lam := by
    simpa using CriticalSequence.iterate_mem_limit hδ h hκ (by simp : (0 : V) ∈ ω)
  -- the pointwise image of the fixed limit
  set A : V := imageSet f lam with hAdef
  have hAsub : A ⊆ lam := h.imageSet_subset_of_value_eq hlim hfix
  have hAcard : lam ≤# A := h.cardLE_imageSet hlim
  -- the restriction of `f` to `lam` and its inverse
  have hr : f ↾ lam ∈ A ^ lam := h.restrict_mem_function hlim
  have hrinj : Injective (f ↾ lam) := h.restrict_injective
  have hrange : range (f ↾ lam) = A := rfl
  have hc : converseGraph (f ↾ lam) ∈ lam ^ A := by
    simpa only [hrange] using converseGraph_mem_function hr hrinj
  set c : V := converseGraph (f ↾ lam) with hcdef
  have hlamdom : lam ⊆ domain f := h.subset_domain hlim
  have hrval : ∀ ξ ∈ lam, (f ↾ lam) ‘ ξ = f ‘ ξ := by
    let := IsFunction.of_mem h.function
    exact fun ξ hξ ↦ value_restrict (hlamdom ξ hξ) hξ
  -- the image function is omega-Jonsson for the same limit
  have hJ' : IsOmegaJonsson (f ‘ F) lam := by
    have := hJ.value_bounded hδ h hF hlim hlamord hωlam hlim2
    rwa [hfix] at this
  obtain ⟨u, hu, huA, ⟨e, he, hre⟩, hval⟩ := hJ'.2.2 A hAsub hAcard κ hκlam
  -- pull the enumeration of `u` back along the inverse of `f ↾ lam`
  let := IsFunction.of_mem he
  have heA : e ∈ A ^ (ω : V) := mem_function_mono' he huA
  have hgb : compose e c ∈ lam ^ (ω : V) := compose_function heA hc
  let := IsFunction.of_mem hgb
  set b : V := range (compose e c) with hbdef
  have hbfun : compose e c ∈ b ^ (ω : V) :=
    function_mem_of_isFunction' (domain_eq_of_mem_function hgb) rfl
  have hblam : b ⊆ lam := range_subset_of_mem_function hgb
  have hbδ : b ∈ hierarchy δ := subset_mem_hierarchy_limit hδ.successor_closed hlim hblam
  have hgbδ : compose e c ∈ hierarchy δ :=
    (hierarchy_transitive δ).mem_trans hbfun
      (function_mem_hierarchy_limit hδ.successor_closed hω hbδ)
  -- values of the pulled back enumeration
  have hgbval : ∀ n ∈ (ω : V), (compose e c) ‘ n = c ‘ (e ‘ n) :=
    fun n hn ↦ value_compose_of_mem_function heA hc hn
  -- `f` maps `b` onto `u` pointwise
  have himg : imageSet f b = u := by
    apply SetTheory.subset_antisymm
    · intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := (h.mem_imageSet_value_iff hbδ y).mp hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp hξ
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function hgb] using mem_domain_of_kpair_mem hn
      have hξv : ξ = c ‘ (e ‘ n) := (value_eq_of_kpair_mem hn).symm.trans (hgbval n hnω)
      have hen : e ‘ n ∈ u := function_value_mem he hnω
      have hrec : (f ↾ lam) ‘ (c ‘ (e ‘ n)) = e ‘ n :=
        value_converseGraph_value hr hrinj (by rw [hrange]; exact huA _ hen)
      rw [hξv, ← hrval _ (function_value_mem hc (huA _ hen)), hrec]
      exact hen
    · intro y hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp (hre.symm ▸ hy)
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hn
      have hyv : e ‘ n = y := value_eq_of_kpair_mem hn
      have hcy : c ‘ y ∈ lam := function_value_mem hc (huA _ (hyv ▸ function_value_mem he hnω))
      refine (h.mem_imageSet_value_iff hbδ y).mpr ⟨c ‘ y, ?_, ?_⟩
      · rw [hbdef, ← hyv, ← hgbval n hnω]
        exact value_mem_range hgb (by simpa [domain_eq_of_mem_function hgb] using hnω)
      · rw [← hrval _ hcy]
        exact value_converseGraph_value hr hrinj
          (by rw [hrange, ← hyv]; exact huA _ (function_value_mem he hnω))
  have hvb : f ‘ b = u := by
    rw [h.value_eq_imageSet_of_omega_surjection hω hbδ hgbδ hbfun rfl]
    exact himg
  -- transfer membership in the domain back through `f`
  have hFfun : IsFunction F := hJ.1
  have hdomF : domain F ∈ hierarchy δ := Cn.domain_closed hδ hF
  have hdomval := h.value_function_domain hF hdomF hFfun rfl
  have hbdom : b ∈ domain F := by
    have : f ‘ b ∈ f ‘ (domain F) := by rw [hvb]; rw [hdomval.2] at hu; exact hu
    exact (h.value_mem_iff hbδ hdomF).mp this
  -- the critical point lands in the pointwise image of the limit
  have happ : (f ‘ F) ‘ (f ‘ b) = f ‘ (F ‘ b) :=
    h.value_apply hF hdomF hFfun rfl hbdom
  have hκv : f ‘ (F ‘ b) = κ := by rw [← happ, hvb]; exact hval
  have hFb : F ‘ b ∈ lam := (hJ.2.1 b hbdom).2
  exact criticalPoint_not_mem_imageSet h hκ hlamord hlim
    ((h.mem_imageSet_value_iff hlim κ).mpr ⟨F ‘ b, hFb, hκv⟩)

/-- Packaged form at `C(1)`: no member of the stage is an omega-Jonsson function for the critical
limit. -/
theorem no_omegaJonsson_selfEmbedding_bounded {δ f κ : V} (hδ : Cn 1 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hlim2 : succ (succ (criticalLimit f κ)) ∈ δ)
    (hJ : ∃ F ∈ hierarchy δ, IsOmegaJonsson F (criticalLimit f κ)) : False := by
  obtain ⟨F, hF, hFJ⟩ := hJ
  exact false_of_omegaJonsson_criticalLimit_bounded hδ h hκ hlim2 hF hFJ

/-- An embedding between rank stages that fixes a `C(1)` ordinal `η` above its critical point, with
the critical limit plus two successors below `η`, admits no omega-Jonsson function for that limit
in `hierarchy η`. -/
theorem false_of_fixed_stage_embedding_bounded {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε) (hηc : Cn 1 η)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η)
    (hlimη : succ (succ (criticalLimit f κ)) ∈ η)
    (hJ : ∃ F ∈ hierarchy η, IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hη
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) :=
    selfRestriction_of_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ :=
    criticalPoint_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ :=
    criticalLimit_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  exact no_omegaJonsson_selfEmbedding_bounded hηc hg hκg (by rw [heq]; exact hlimη)
    (by rw [heq]; exact hJ)

/-- Kunen's contradiction under choice at a fixed stage, with `η` only assumed to be in `C(1)`. -/
theorem false_of_fixed_stage_embedding_choice_one (hAC : InternalChoice V) {k l : ℕ}
    {δ ε f η κ : V} (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε) (hηc : Cn 1 η)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η)
    (hlimη : succ (succ (criticalLimit f κ)) ∈ η) : False := by
  let := hη
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) :=
    selfRestriction_of_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ :=
    criticalPoint_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ :=
    criticalLimit_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  let := CriticalSequence.limit_ordinal hηc hg hκg
  have hlimδ : criticalLimit (f ↾ (hierarchy η)) κ ∈ η := by
    rw [heq]
    exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (criticalLimit f κ))
      (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ (criticalLimit f κ))) hlimη)
  have hlim : criticalLimit (f ↾ (hierarchy η)) κ ∈ hierarchy η :=
    ordinal_mem_hierarchy_iff.mpr hlimδ
  exact no_omegaJonsson_selfEmbedding_bounded hηc hg hκg (by rw [heq]; exact hlimη)
    (exists_omegaJonsson_criticalLimit hAC hηc hg hκg hlim)

end ZFVP
