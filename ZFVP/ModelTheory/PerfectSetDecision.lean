import ZFVP.ModelTheory.SplittingNameTransfer
import ZFVP.ModelTheory.DecidedName
import ZFVP.ModelTheory.FilterDecision
import ZFVP.ModelTheory.LevySmallSetLocalization
import ZFVP.ModelTheory.LevyCollapseOmegaOne
import ZFVP.SetTheory.MeasurableStrongLimit

/-! The perfect set property for sets of reals of the Levy extension definable from ground
parameters, over an arbitrary ground model. A definable set either consists of ground reals, hence
is countable, or contains a real `x` new over the ground. The real `x` lies in a bounded stage
`V[G_ξ]`; the decided segments of its `Coll(ω, <ξ)`-name form a splitting scheme below a condition
`p₁` in the generic which also lies in the decision set of the defining formula. Every filter of the
cone through the ground dense sets then yields a real in the set, so the set contains a perfect
subset. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem decidedSegment_definable (P R one τ : V) : ℒₛₑₜ-function₁[V] (decidedSegment P R one τ) := by
  have h : ℒₛₑₜ-relation (fun D q : V ↦ ∀ z, z ∈ D ↔
      z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ∧ IsDecided P R one τ q z) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = decidedSegment P R one τ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_decidedSegment_iff]

theorem upwardPredicate_definable (F R : V) : ℒₛₑₜ-predicate (fun q : V ↦ ∃ p ∈ F, ⟨p, q⟩ₖ ∈ R) := by
  definability

section

variable {P R one : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  {τ : V} (hτ : IsForcingName P τ) {p₀ : V} (hp₀ : p₀ ∈ P)
  (hnew : p₀ ∈ forcingFormula P R newRealFormula (standardTuple ![τ, checkName one (cantorSpace V)]))

include hR htop hτ hp₀ hnew in
/-- A generic through `p₀` meets every decider set. -/
theorem decider_in_generic {G' : Set V} (hG' : IsExternalForcingGeneric P R G') (hp₀G : p₀ ∈ G')
    (n : V) (hn : n ∈ (ω : V)) : ∃ q ∈ G', q ∈ deciderSet P R one τ n := by
  have hdense := forcing_decisions_dense hR (sep_subset : deciderSet P R one τ n ⊆ P)
  obtain ⟨q, hqG, hqD⟩ := hG'.2 _ hdense
  rcases mem_union_iff.mp hqD with h | h
  · exact ⟨q, hqG, h⟩
  · exfalso
    obtain ⟨hqP, hneg⟩ := (mem_forcingNegation_iff _ _ _ _).mp h
    obtain ⟨q', hq'G, hq'q, hq'p₀⟩ := hG'.1.2.2.2 q hqG p₀ hp₀G
    have hq'P : q' ∈ P := hG'.1.1 q' hq'G
    obtain ⟨r, hrD, hrq'⟩ := decider_dense_unrestricted hR htop hτ hp₀ hnew n hn q' hq'P hq'p₀
    have hrP : r ∈ P := ((mem_deciderSet_iff _ _ _ _ _ _).mp hrD).1
    exact hneg r hrP (hR.2.2 r hrP q' hq'P q hqP hrq' hq'q) hrD

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
theorem levy_ground_reals_countable : IsInternallyCountable ((levyContext κ hG).check (cantorSpace V)) := by
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hω (omega_prod_two_cardLE (V := V))
  have hsub : cantorSpace V ≤# ν :=
    (cardLE_of_subset (fun x hx ↦ mem_power_iff.mpr (mem_function_iff.mp hx).1)).trans hpow
  exact internallyCountable_of_cardLE (levy_check_countable hG hν) ((levyContext κ hG).checkEmbedding.map_cardLE hsub)

include hAC hU hc hω in
theorem levy_coneDenseSets_countable {ξ : V} (hξ : ξ ∈ κ) (R p₁ : V) :
    IsInternallyCountable ((levyContext κ hG).check (coneDenseSets (levyCollapse ξ) R p₁)) := by
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  obtain ⟨μ, hμ, hpow⟩ := power_small_of_measurable hAC hU hc hν hsmall
  have h := (cardLE_of_subset (coneDenseSets_subset_power _ R p₁)).trans hpow
  exact internallyCountable_of_cardLE (levy_check_countable hG hμ) ((levyContext κ hG).checkEmbedding.map_cardLE h)

include hAC hU hc hω hκ in
/-- Every set of reals of the Levy extension of an arbitrary ground definable from ground
parameters has the perfect set property. -/
theorem perfectSetProperty_of_ground_definable {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (a : Fin n → V) {X : (levyContext κ hG).Model}
    (hX : ∀ x, x ∈ X ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i))) :
    PerfectSetProperty X := by
  let W := levyContext κ hG
  by_cases hsub : X ⊆ W.check (cantorSpace V)
  · left
    exact internallyCountable_subset (levy_ground_reals_countable hAC hU hc hω hG) hsub
  right
  obtain ⟨x, hxX, hxnew⟩ : ∃ x ∈ X, x ∉ W.check (cantorSpace V) := by
    by_contra h
    exact hsub (fun x hx ↦ by_contra (fun hn ↦ h ⟨x, hx, hn⟩))
  obtain ⟨hxc, hxφ⟩ := (hX x).mp hxX
  have hxc' : x ∈ W.check ((2 : ℕ) : V) ^ W.check (ω : V) := by rw [← cantorSpace_eq_check]; exact hxc
  have hx2 : x ⊆ W.check (ω : V) ×ˢ W.check ((2 : ℕ) : V) := (mem_function_iff.mp hxc').1
  have hxsub : x ⊆ W.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := by
    have hprod : W.check ((ω : V) ×ˢ ((2 : ℕ) : V)) = W.check (ω : V) ×ˢ W.check ((2 : ℕ) : V) :=
      W.checkEmbedding.map_prod _ _
    rw [hprod]
    exact hx2
  obtain ⟨ξ, hξ, y, hy⟩ := levy_subset_check_localized hAC hU hc hω hκ hG omega_prod_two_cardLE hω x hxsub
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  let A := levySubContext ξ hξ' hG
  let L := levySubRealization ξ hξ' hG
  have hLground : ∀ b : V, L.ground b = W.check b := levySubRealization_ground ξ hξ' hG
  have hvc : ∀ b : V, L.value (A.check b) = W.check b := fun b ↦ (L.value_check b).trans (hLground b)
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  have hR : IsForcingPreorder A.P A.R := A.order
  have htop : IsForcingTop A.P A.R A.one := A.top
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have hAPsmall : A.P ≤# ν := hsmall
  -- the name `τ` names a new real
  have hyc : A.ofName τ ∈ cantorSpace A.Model := by
    rw [cantorSpace_eq_check]
    have h := hxc'
    rw [← hy, ← hvc, ← hvc] at h
    exact (L.embedding.function_iff (A.ofName τ) (A.check (ω : V)) (A.check ((2 : ℕ) : V))).mp h
  have hynew : A.ofName τ ∉ A.check (cantorSpace V) := fun h ↦
    hxnew (by rw [← hy, ← hvc]; exact (L.value_mem_iff _ _).mpr h)
  have htruth := A.formula_truth newRealFormula
    ![τ, ⟨checkName A.one (cantorSpace V), checkName_isName A.top.1 _⟩]
  have hv : (fun i ↦ ((![τ, ⟨checkName A.one (cantorSpace V), checkName_isName A.top.1 _⟩] :
      Fin 2 → ForcingName A.P) i).val) = ![τ.val, checkName A.one (cantorSpace V)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i
  rw [hv, eval_newRealFormula] at htruth
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htruth
  obtain ⟨p₀, hp₀G, hnew⟩ := htruth.mp ⟨hyc, hynew⟩
  have hp₀ : p₀ ∈ A.P := A.generic.1.1 p₀ hp₀G
  have hτ : IsForcingName A.P τ.val := τ.property
  -- the nice name of the decided real
  obtain ⟨σ, hσdef⟩ : ∃ σ : V, σ = decidedName A.P A.R A.one τ.val := ⟨_, rfl⟩
  have hσ : IsForcingName A.P σ := by rw [hσdef]; exact decidedName_isName _ _ A.top.1
  -- the generic of the stage as a filter of the extension
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : W.Model, H₀ = L.genericSet := ⟨_, rfl⟩
  have hH₀mem : ∀ q, W.check q ∈ H₀ ↔ q ∈ A.G := by
    intro q
    rw [hH₀, ← hLground]
    exact L.generic_mem q
  have hH₀sub : H₀ ⊆ W.check A.P := by
    rw [hH₀, ← hLground]
    exact L.generic_subset
  have hH₀filter : IsForcingFilter (W.check A.P) (W.check A.R) H₀ := by
    have := L.filter
    rw [hLground, hLground] at this
    rw [hH₀]
    exact this
  have hH₀gen : ∀ D : V, ForcingDense A.P A.R D → ∃ q ∈ D, W.check q ∈ H₀ := by
    intro D hD
    obtain ⟨q, hqG, hqD⟩ := A.generic.2 D hD
    exact ⟨q, hqD, (hH₀mem q).mpr hqG⟩
  have hH₀loc : IsLocalized hG H₀ := ⟨ξ, hξ, A.genericSet, by rw [hH₀]; exact L.value_genericSet⟩
  have hone₀ : W.check A.one ∈ H₀ :=
    (hH₀mem _).mpr (A.generic.1.2.2.1 p₀ hp₀G A.one A.top.1 (A.top.2 p₀ hp₀))
  -- `x` is the value of the decided name under the generic
  have hxval : nameValue H₀ (W.check σ) = x := by
    apply mem_ext
    intro z
    rw [hσdef, W.mem_nameValue_check_decidedName_iff hR hone₀]
    constructor
    · rintro ⟨q, hqH, z', hz', rfl⟩
      have hqG := (hH₀mem q).mp hqH
      obtain ⟨-, m, hm, i, hi, rfl, hf, -⟩ := (mem_decidedSegment_iff _ _ _ _ _ _).mp hz'
      have hmem : A.check ⟨m, i⟩ₖ ∈ A.ofName τ := (A.checkedMember_truth τ _).mpr ⟨q, hqG, hf⟩
      rw [← hy, ← hvc]
      exact (L.value_mem_iff _ _).mpr hmem
    · intro hz
      obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp (hx2 z hz)
      obtain ⟨m, hm, rfl⟩ := (W.mem_check_iff _ _).mp ha'
      obtain ⟨i, hi, rfl⟩ := (W.mem_check_iff _ _).mp hb'
      rw [← W.check_kpair] at hz
      have hzA : A.check ⟨m, i⟩ₖ ∈ A.ofName τ := by
        rw [← hy, ← hvc] at hz
        exact (L.value_mem_iff _ _).mp hz
      obtain ⟨q₁, hq₁G, hf₁⟩ := (A.checkedMember_truth τ _).mp hzA
      obtain ⟨q₃, hq₃G, hq₃D⟩ := decider_in_generic hR htop hτ hp₀ hnew A.generic hp₀G m hm
      obtain ⟨q₄, hq₄G, hq₄q₃, hq₄q₁⟩ := A.generic.1.2.2.2 q₃ hq₃G q₁ hq₁G
      have hq₄P : q₄ ∈ A.P := A.generic.1.1 q₄ hq₄G
      obtain ⟨-, hdec₃⟩ := (mem_deciderSet_iff _ _ _ _ _ _).mp hq₃D
      refine ⟨q₄, (hH₀mem q₄).mpr hq₄G, ⟨m, i⟩ₖ, ?_, (W.check_kpair m i).symm⟩
      refine (mem_decidedSegment_iff _ _ _ _ _ _).mpr ⟨mem_prod_iff.mpr ⟨m, hm, i, hi, rfl⟩,
        m, hm, i, hi, rfl, forcesCheckedMember_mono hR hq₄P hq₄q₁ hf₁, fun m' hm' ↦ ?_⟩
      obtain ⟨i', hi', hf'⟩ := hdec₃ m' (mem_succ_iff.mpr (Or.inr hm'))
      exact ⟨i', hi', forcesCheckedMember_mono hR hq₄P hq₄q₃ hf'⟩
  -- the decision condition
  have hdecision := filter_decision hAC hU hc hω hκ hG hR htop hH₀sub hH₀filter hH₀gen hH₀loc hσ φ a
  rw [hxval] at hdecision
  obtain ⟨q₁, hq₁H, hq₁D⟩ := hdecision.mp hxφ
  have hq₁G := (hH₀mem q₁).mp hq₁H
  obtain ⟨p₁, hp₁G, hp₁q₁, hp₁p₀⟩ := A.generic.1.2.2.2 q₁ hq₁G p₀ hp₀G
  have hp₁P : p₁ ∈ A.P := A.generic.1.1 p₁ hp₁G
  -- the splitting scheme on the cone below `p₁`
  obtain ⟨Pc, hPc⟩ : ∃ Pc : V, Pc = cone A.P A.R p₁ := ⟨_, rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : V, Rc = restrictedOrder A.R Pc := ⟨_, rfl⟩
  have hPcsub : Pc ⊆ A.P := by rw [hPc]; exact cone_subset _ _ _
  have hmemPc : ∀ q, q ∈ Pc ↔ q ∈ A.P ∧ ⟨q, p₁⟩ₖ ∈ A.R := by
    intro q
    rw [hPc]
    exact mem_cone_iff _ _ _ _
  have hmemRc : ∀ p q, ⟨p, q⟩ₖ ∈ Rc ↔ ⟨p, q⟩ₖ ∈ A.R ∧ p ∈ Pc ∧ q ∈ Pc := by
    intro p q
    rw [hRc]
    exact kpair_mem_restrictedOrder_iff _ _ _ _
  have hRcpre : IsForcingPreorder Pc Rc := by rw [hRc, hPc]; exact cone_preorder hR p₁
  have hbelow : ∀ q ∈ Pc, ⟨q, p₀⟩ₖ ∈ A.R := fun q hq ↦
    hR.2.2 q (hPcsub q hq) p₁ hp₁P p₀ hp₀ ((hmemPc q).mp hq).2 hp₁p₀
  have hp₁c : p₁ ∈ Pc := (hmemPc p₁).mpr ⟨hp₁P, hR.2.1 p₁ hp₁P⟩
  have hsegfun : ∀ q ∈ Pc, decidedSegment A.P A.R A.one τ.val q ∈ binarySequences V := fun q hq ↦
    decidedSegment_mem_binarySequences_unrestricted hR htop hτ hp₀ hnew (hPcsub q hq) (hbelow q hq)
  obtain ⟨graph, hgraphdef⟩ : ∃ g : V, g = definableGraph Pc (decidedSegment A.P A.R A.one τ.val)
    (decidedSegment_definable _ _ _ _) := ⟨_, rfl⟩
  have hgraph : graph ∈ binarySequences V ^ Pc := by
    rw [hgraphdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ hsegfun
  have hgraphval : ∀ q ∈ Pc, graph ‘ q = decidedSegment A.P A.R A.one τ.val q := by
    intro q hq
    rw [hgraphdef]
    exact value_definableGraph _ _ _ hq
  have hgraphfun : IsFunction graph := IsFunction.of_mem hgraph
  have hRW : IsForcingPreorder (W.check Pc) (W.check Rc) := W.check_forcingPreorder hRcpre
  have hRW' : IsForcingPreorder (W.check A.P) (W.check A.R) := W.check_forcingPreorder hR
  have hp₁W : W.check p₁ ∈ W.check Pc := (W.check_mem_iff _ _).mpr hp₁c
  have hτW : W.check graph ∈ binarySequences W.Model ^ W.check Pc := by
    rw [← W.check_binarySequences]
    exact (W.check_function_iff _ _ _).mpr hgraph
  have hτWfun : IsFunction (W.check graph) := IsFunction.of_mem hτW
  have hval : ∀ q ∈ Pc, (W.check graph) ‘ (W.check q) = W.check (decidedSegment A.P A.R A.one τ.val q) := by
    intro q hq
    rw [W.check_value (by rw [domain_eq_of_mem_function hgraph]; exact hq), hgraphval q hq]
  have hRcW : ∀ p q, ⟨W.check p, W.check q⟩ₖ ∈ W.check Rc ↔ ⟨p, q⟩ₖ ∈ Rc := by
    intro p q
    rw [← W.check_kpair, W.check_mem_iff]
  have hmono : ∀ p ∈ W.check Pc, ∀ q ∈ W.check Pc, ⟨q, p⟩ₖ ∈ W.check Rc →
      (W.check graph) ‘ p ⊆ (W.check graph) ‘ q := by
    intro p hp q hq hqp
    obtain ⟨p', hp', rfl⟩ := (W.mem_check_iff _ _).mp hp
    obtain ⟨q', hq', rfl⟩ := (W.mem_check_iff _ _).mp hq
    obtain ⟨hq'p', -, -⟩ := (hmemRc q' p').mp ((hRcW q' p').mp hqp)
    rw [hval p' hp', hval q' hq']
    exact (W.checkEmbedding.subset_iff _ _).mpr (decidedSegment_mono hR (hPcsub q' hq') hq'p')
  have hsplit : ∀ p ∈ W.check Pc, ∃ q ∈ W.check Pc, ∃ q' ∈ W.check Pc,
      ⟨q, p⟩ₖ ∈ W.check Rc ∧ ⟨q', p⟩ₖ ∈ W.check Rc ∧
      Incompatible ((W.check graph) ‘ q) ((W.check graph) ‘ q') := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := (W.mem_check_iff _ _).mp hp
    obtain ⟨q, hqP, q', hq'P, hqp', hq'p', hinc⟩ :=
      decidedSegment_split_unrestricted hR htop hτ hp₀ hnew (hPcsub p' hp') (hbelow p' hp')
    have hqc : q ∈ Pc := (hmemPc q).mpr ⟨hqP, hR.2.2 q hqP p' (hPcsub p' hp') p₁ hp₁P hqp' ((hmemPc p').mp hp').2⟩
    have hq'c : q' ∈ Pc := (hmemPc q').mpr ⟨hq'P, hR.2.2 q' hq'P p' (hPcsub p' hp') p₁ hp₁P hq'p' ((hmemPc p').mp hp').2⟩
    refine ⟨W.check q, (W.check_mem_iff _ _).mpr hqc, W.check q', (W.check_mem_iff _ _).mpr hq'c,
      (hRcW q p').mpr ((hmemRc q p').mpr ⟨hqp', hqc, hp'⟩),
      (hRcW q' p').mpr ((hmemRc q' p').mpr ⟨hq'p', hq'c, hp'⟩), ?_⟩
    rw [hval q hqc, hval q' hq'c]
    have := binarySequence_isFunction (hsegfun q hqc)
    have := binarySequence_isFunction (hsegfun q' hq'c)
    exact W.check_incompatible hinc
  -- the enumeration of the ground dense subsets of the cone
  have hcount : IsInternallyCountable (W.check (coneDenseSets A.P A.R p₁)) :=
    levy_coneDenseSets_countable hAC hU hc hω hG hξ A.R p₁
  obtain ⟨e, he, hedense, heenum⟩ := W.exists_cone_dense_enumeration hR p₁ hcount
  rw [← hPc] at he
  rw [← hPc, ← hRc] at hedense
  have hdense : ∀ m ∈ (ω : W.Model), ∀ p ∈ W.check Pc, ∃ q ∈ e ‘ m, ⟨q, p⟩ₖ ∈ W.check Rc :=
    fun m hm p hp ↦ (hedense m hm).2 p hp
  have hconeDense : ∀ D : V, D ∈ coneDenseSets A.P A.R p₁ → ∃ m ∈ (ω : W.Model), e ‘ m = W.check D := heenum
  -- every filter of the cone through the dense sets gives a real in `X`
  have hA : ∀ F, IsForcingFilter (W.check Pc) (W.check Rc) F → W.check p₁ ∈ F →
      (∀ m ∈ (ω : W.Model), ∃ q ∈ F, q ∈ e ‘ m) → ⋃ˢ (image (W.check graph) F) ∈ X := by
    intro F hF hp₁F hmeets
    obtain ⟨F', hF'def⟩ : ∃ F' : W.Model, F' = sep (W.check A.P) (fun q ↦ ∃ p ∈ F, ⟨p, q⟩ₖ ∈ W.check A.R)
      (upwardPredicate_definable F (W.check A.R)) := ⟨_, rfl⟩
    have hF'mem : ∀ q, q ∈ F' ↔ q ∈ W.check A.P ∧ ∃ p ∈ F, ⟨p, q⟩ₖ ∈ W.check A.R := by
      intro q
      rw [hF'def]
      exact mem_sep_iff
    have hFcheck : ∀ p ∈ F, ∃ p' ∈ Pc, p = W.check p' := fun p hp ↦ (W.mem_check_iff _ _).mp (hF.1 p hp)
    have hFP : ∀ p ∈ F, p ∈ W.check A.P := fun p hp ↦
      (W.checkEmbedding.subset_iff Pc A.P).mpr hPcsub p (hF.1 p hp)
    have hRcR : ∀ p q, ⟨p, q⟩ₖ ∈ W.check Rc → ⟨p, q⟩ₖ ∈ W.check A.R := by
      intro p q h
      rw [hRc, W.check_restrictedOrder] at h
      exact ((kpair_mem_restrictedOrder_iff _ _ _ _).mp h).1
    have hF'sub : F' ⊆ W.check A.P := fun q hq ↦ ((hF'mem q).mp hq).1
    have hFF' : ∀ p ∈ F, p ∈ F' := fun p hp ↦
      (hF'mem p).mpr ⟨hFP p hp, p, hp, hRW'.2.1 p (hFP p hp)⟩
    have hF'filter : IsForcingFilter (W.check A.P) (W.check A.R) F' := by
      refine ⟨hF'sub, ⟨W.check p₁, hFF' _ hp₁F⟩, fun q hq r hr hqr ↦ ?_, fun q₁ hq₁ q₂ hq₂ ↦ ?_⟩
      · obtain ⟨hqP, p, hpF, hpq⟩ := (hF'mem q).mp hq
        exact (hF'mem r).mpr ⟨hr, p, hpF, hRW'.2.2 p (hFP p hpF) q hqP r hr hpq hqr⟩
      · obtain ⟨hq₁P, p₁', hp₁'F, hp₁'q₁⟩ := (hF'mem q₁).mp hq₁
        obtain ⟨hq₂P, p₂', hp₂'F, hp₂'q₂⟩ := (hF'mem q₂).mp hq₂
        obtain ⟨r, hrF, hrp₁', hrp₂'⟩ := hF.2.2.2 p₁' hp₁'F p₂' hp₂'F
        refine ⟨r, hFF' r hrF, ?_, ?_⟩
        · exact hRW'.2.2 r (hFP r hrF) p₁' (hFP p₁' hp₁'F) q₁ hq₁P (hRcR _ _ hrp₁') hp₁'q₁
        · exact hRW'.2.2 r (hFP r hrF) p₂' (hFP p₂' hp₂'F) q₂ hq₂P (hRcR _ _ hrp₂') hp₂'q₂
    have hF'meet : ∀ D : V, D ∈ coneDenseSets A.P A.R p₁ → ∃ q ∈ D, W.check q ∈ F' := by
      intro D hD
      obtain ⟨m, hm, hem⟩ := hconeDense D hD
      obtain ⟨q, hqF, hqe⟩ := hmeets m hm
      rw [hem] at hqe
      obtain ⟨q', hq'D, rfl⟩ := (W.mem_check_iff _ _).mp hqe
      exact ⟨q', hq'D, hFF' _ hqF⟩
    have hF'gen : ∀ D : V, ForcingDense A.P A.R D → ∃ q ∈ D, W.check q ∈ F' := by
      intro D hD
      have hD' : D ∩ Pc ∈ coneDenseSets A.P A.R p₁ := by
        rw [hPc]
        exact (mem_coneDenseSets_iff _ _ _ _).mpr ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, cone_dense hR hp₁P hD⟩
      obtain ⟨q, hq, hqF'⟩ := hF'meet _ hD'
      exact ⟨q, (mem_inter_iff.mp hq).1, hqF'⟩
    have hF'loc : IsLocalized hG F' := levy_subset_check_localized hAC hU hc hω hκ hG hAPsmall hν F' hF'sub
    have hq₁F' : W.check q₁ ∈ F' := (hF'mem _).mpr ⟨(W.check_mem_iff _ _).mpr (A.generic.1.1 q₁ hq₁G),
      W.check p₁, hp₁F, by rw [← W.check_kpair, W.check_mem_iff]; exact hp₁q₁⟩
    have hφF : φ.Evalb (nameValue F' (W.check σ) :> fun i ↦ W.check (a i)) :=
      (filter_decision hAC hU hc hω hκ hG hR htop hF'sub hF'filter hF'gen hF'loc hσ φ a).mpr ⟨q₁, hq₁F', hq₁D⟩
    have honeF' : W.check A.one ∈ F' := hF'filter.2.2.1 _ (hFF' _ hp₁F) _ ((W.check_mem_iff _ _).mpr A.top.1)
      (by rw [← W.check_kpair, W.check_mem_iff]; exact A.top.2 p₁ hp₁P)
    have hY : ∀ z, z ∈ nameValue F' (W.check σ) ↔
        ∃ q, W.check q ∈ F' ∧ ∃ z' ∈ decidedSegment A.P A.R A.one τ.val q, z = W.check z' := by
      intro z
      rw [hσdef]
      exact W.mem_nameValue_check_decidedName_iff hR honeF' z
    -- the union of the segments along `F` is the value of the decided name under `F'`
    have hunion : ⋃ˢ (image (W.check graph) F) = nameValue F' (W.check σ) := by
      apply mem_ext
      intro z
      rw [hY, mem_sUnion_iff]
      constructor
      · rintro ⟨y, hy, hzy⟩
        obtain ⟨p, hpF, hpy⟩ := (mem_image_iff' _ _ _).mp hy
        obtain ⟨p', hp'c, rfl⟩ := hFcheck p hpF
        have hyeq : y = W.check (decidedSegment A.P A.R A.one τ.val p') := by
          rw [← hval p' hp'c]
          exact (value_eq_of_kpair_mem hpy).symm
        rw [hyeq] at hzy
        obtain ⟨z', hz', rfl⟩ := (W.mem_check_iff _ _).mp hzy
        exact ⟨p', hFF' _ hpF, z', hz', rfl⟩
      · rintro ⟨q, hqF', z', hz', rfl⟩
        obtain ⟨hqP, p, hpF, hpq⟩ := (hF'mem _).mp hqF'
        obtain ⟨p', hp'c, rfl⟩ := hFcheck p hpF
        have hp'q : ⟨p', q⟩ₖ ∈ A.R := by
          rw [← W.check_kpair, W.check_mem_iff] at hpq
          exact hpq
        have hqP' : q ∈ A.P := (W.check_mem_iff _ _).mp hqP
        have hz'p' : z' ∈ decidedSegment A.P A.R A.one τ.val p' :=
          decidedSegment_mono hR (hPcsub p' hp'c) hp'q z' hz'
        refine ⟨(W.check graph) ‘ (W.check p'), (mem_image_iff' _ _ _).mpr ⟨W.check p', hpF, ?_⟩, ?_⟩
        · exact kpair_value_mem (by rw [domain_eq_of_mem_function hτW]; exact hF.1 _ hpF)
        · rw [hval p' hp'c, W.check_mem_iff]
          exact hz'p'
    rw [hunion]
    refine (hX _).mpr ⟨?_, hφF⟩
    refine W.decided_union_real hR (p₀ := p₀) (fun q hq hqp₀ ↦
      decidedSegment_mem_binarySequences_unrestricted hR htop hτ hp₀ hnew hq hqp₀) (fun q hq ↦
      (W.check_mem_iff _ _).mp (hF'sub _ hq)) ?_ ?_ hY
    · intro q₁' q₂' hq₁' hq₂'
      obtain ⟨-, p₁', hp₁'F, hp₁'q₁⟩ := (hF'mem _).mp hq₁'
      obtain ⟨-, p₂', hp₂'F, hp₂'q₂⟩ := (hF'mem _).mp hq₂'
      obtain ⟨r, hrF, hrp₁', hrp₂'⟩ := hF.2.2.2 p₁' hp₁'F p₂' hp₂'F
      obtain ⟨r', hr'c, rfl⟩ := hFcheck r hrF
      have hr'P : r' ∈ A.P := hPcsub r' hr'c
      have h1 : ⟨r', q₁'⟩ₖ ∈ A.R := by
        have := hRW'.2.2 _ (hFP _ hrF) p₁' (hFP p₁' hp₁'F) _ ((W.check_mem_iff _ _).mpr
          ((W.check_mem_iff _ _).mp ((hF'mem _).mp hq₁').1)) (hRcR _ _ hrp₁') hp₁'q₁
        rw [← W.check_kpair, W.check_mem_iff] at this
        exact this
      have h2 : ⟨r', q₂'⟩ₖ ∈ A.R := by
        have := hRW'.2.2 _ (hFP _ hrF) p₂' (hFP p₂' hp₂'F) _ ((W.check_mem_iff _ _).mpr
          ((W.check_mem_iff _ _).mp ((hF'mem _).mp hq₂').1)) (hRcR _ _ hrp₂') hp₂'q₂
        rw [← W.check_kpair, W.check_mem_iff] at this
        exact this
      exact ⟨r', hFF' _ hrF, h1, h2, hbelow r' hr'c⟩
    · intro m hm
      have hD : deciderSet A.P A.R A.one τ.val m ∩ Pc ∈ coneDenseSets A.P A.R p₁ := by
        rw [hPc]
        refine (mem_coneDenseSets_iff _ _ _ _).mpr ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, ?_⟩
        exact cone_dense_of_below hR hp₁P sep_subset (fun q hq hqp₁ ↦
          decider_dense_unrestricted hR htop hτ hp₀ hnew m hm q hq (hR.2.2 q hq p₁ hp₁P p₀ hp₀ hqp₁ hp₁p₀))
      obtain ⟨q, hq, hqF'⟩ := hF'meet _ hD
      exact ⟨q, (mem_inter_iff.mp hq).1, hqF'⟩
  exact exists_perfectTree_of_splitting (W.internalChoice_of_ground hAC) hRW hp₁W hτW hmono hsplit he hdense hA

end

end ZFVP
