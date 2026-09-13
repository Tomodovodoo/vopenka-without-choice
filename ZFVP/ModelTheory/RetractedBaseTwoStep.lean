import ZFVP.ModelTheory.NormalizedNameTransportBounds
import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.EquivalentRetractionAtoms
import ZFVP.SetTheory.EquivalentRetractionForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The bounded presentation whose prefix and name conditions lie in the
specified equivalent suborder of the preceding forcing. -/
noncomputable def retractedBaseTwoStep (P R δ Q N : V) : V :=
  {z ∈ boundedNameTwoStep P R δ Q ; kpair.π₁ z ∈ N ∧ IsForcingName N (kpair.π₂ z)}

noncomputable def retractedBaseTwoStepCode (m z : V) : V :=
  ⟨m ‘ (kpair.π₁ z), nameAction m (kpair.π₂ z)⟩ₖ

instance retractedBaseTwoStepCode_definable (m : V) :
    ℒₛₑₜ-function₁[V] (retractedBaseTwoStepCode m) := by
  unfold retractedBaseTwoStepCode
  definability

@[simp] theorem retractedBaseTwoStepCode_pair (m p τ : V) :
    retractedBaseTwoStepCode m ⟨p, τ⟩ₖ = ⟨m ‘ p, nameAction m τ⟩ₖ := by
  simp [retractedBaseTwoStepCode]

theorem retractedBaseTwoStep_subset (P R δ Q N : V) :
    retractedBaseTwoStep P R δ Q N ⊆ boundedNameTwoStep P R δ Q := sep_subset

theorem retractedBaseTwoStepCode_mem {P R δ Q N m z : V}
    (hR : IsForcingPreorder P R) (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy δ) (hN : N ⊆ P) (hm : m ∈ N ^ P)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hz : z ∈ boundedNameTwoStep P R δ Q) :
    retractedBaseTwoStepCode m z ∈ retractedBaseTwoStep P R δ Q N := by
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hp, hτδ, hτ, hτQ⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
  have hpn := function_value_mem hm hp
  have hτn := nameAction_isName hm hτ
  have heτ := nameAction_forced_equal_of_equivalent_conditions hR
    (mem_function_of_mem_function_of_subset hm hN) he hτ p hp
  rw [retractedBaseTwoStepCode_pair, retractedBaseTwoStep, mem_sep_iff]
  refine ⟨(pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr
    ⟨hN _ hpn, suborderNameAction_mem_hierarchy hδ hP hN hm hτ hτδ,
      hτn.mono hN, ?_⟩, ?_⟩
  · exact atomicMembership_mono hR (atomicMembership_subst_left hR heτ hτQ) (hN _ hpn) (he p hp).1
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hpn hτn

theorem retractedBaseTwoStepCode_fixes {P R δ Q N m z : V}
    (hfix : ∀ p ∈ N, m ‘ p = p) (hz : z ∈ retractedBaseTwoStep P R δ Q N) :
    retractedBaseTwoStepCode m z = z := by
  obtain ⟨hb, hn, hτ⟩ := mem_sep_iff.mp hz
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hb).1
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hn hτ
  rw [retractedBaseTwoStepCode_pair, hfix p hn, nameAction_eq_self_of_fixes_conditions hfix hτ]

theorem retractedBaseTwoStepCode_equivalent {P R one δ Q S N m z : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hN : N ⊆ P) (hm : m ∈ N ^ P)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) (hz : z ∈ boundedNameTwoStep P R δ Q) :
    ⟨retractedBaseTwoStepCode m z, z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) ∧
      ⟨z, retractedBaseTwoStepCode m z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  have hz' := retractedBaseTwoStep_subset P R δ Q N _ (retractedBaseTwoStepCode_mem hR hδ hP hN hm he hz)
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hp, _, hτ, hτQ⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
  have heτ := nameAction_forced_equal_of_equivalent_conditions hR
    (mem_function_of_mem_function_of_subset hm hN) he hτ p hp
  have hrefl := forcedPreorder_refl hR ht hp ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩
    ⟨τ, hτ⟩ (hI.preorder p hp) hτQ
  have heττ : p ∈ atomicEquality P R τ τ := (atomicEquality_refl hR τ).symm ▸ hp
  have hleft := (forcingPairMember_congr_names hR hp heτ heττ).mp hrefl
  have hright := (forcingPairMember_congr_names hR hp heττ heτ).mp hrefl
  simp only [retractedBaseTwoStepCode_pair] at hz' ⊢
  exact ⟨(pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr ⟨hz', hz, (he p hp).1,
      (forcingFormula_regular hR boundedPairMemberFormula _).2.1 p hleft _
        (hN _ (function_value_mem hm hp)) (he p hp).1⟩,
    (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr ⟨hz, hz', (he p hp).2, hright⟩⟩

noncomputable def retractedBaseTwoStepMap (P R δ Q m : V) : V :=
  definableGraph (boundedNameTwoStep P R δ Q) (retractedBaseTwoStepCode m) (by infer_instance)

theorem retractedBaseTwoStepMap_value {P R δ Q m z : V} (hz : z ∈ boundedNameTwoStep P R δ Q) :
    (retractedBaseTwoStepMap P R δ Q m) ‘ z = retractedBaseTwoStepCode m z :=
  value_definableGraph _ _ _ hz

theorem retractedBaseTwoStepMap_retraction {P R one δ Q S N m : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hN : N ⊆ P) (hm : m ∈ N ^ P) (hfix : ∀ p ∈ N, m ‘ p = p)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) :
    IsForcingRetraction (retractedBaseTwoStep P R δ Q N)
      (nameTwoStepOrderOn P R S (retractedBaseTwoStep P R δ Q N))
      (boundedNameTwoStep P R δ Q) (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q))
      (retractedBaseTwoStepMap P R δ Q m) := by
  have hmap : retractedBaseTwoStepMap P R δ Q m ∈
      retractedBaseTwoStep P R δ Q N ^ boundedNameTwoStep P R δ Q :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hz ↦ retractedBaseTwoStepCode_mem hR hδ hP hN hm he hz)
  have hsub := retractedBaseTwoStep_subset P R δ Q N
  have hh := equivalentSuborderRetraction_spec
    (boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder) hsub
    (S := nameTwoStepOrderOn P R S (retractedBaseTwoStep P R δ Q N)) ?_ hmap ?_
  · have heq : equivalentSuborderRetraction (boundedNameTwoStep P R δ Q)
        (retractedBaseTwoStep P R δ Q N) (retractedBaseTwoStepMap P R δ Q m) =
          retractedBaseTwoStepMap P R δ Q m := by
      apply function_eq_of_values (equivalentSuborderRetraction_function hmap) hmap
      intro z hz
      rw [equivalentSuborderRetraction_value hz]
      classical
      by_cases hn : z ∈ retractedBaseTwoStep P R δ Q N
      · simp only [equivalentSuborderFix, hn, ↓reduceIte, retractedBaseTwoStepMap_value hz,
          retractedBaseTwoStepCode_fixes hfix hn]
      · simp only [equivalentSuborderFix, hn, ↓reduceIte]
    rwa [heq] at hh
  · intro z hz w hw
    simp only [nameTwoStepOrderOn, mem_sep_iff, kpair_mem_iff, hz, hw, hsub z hz, hsub w hw, true_and]
  · intro z hz
    rw [retractedBaseTwoStepMap_value hz]
    exact retractedBaseTwoStepCode_equivalent hR ht hδ hP hN hm he hI hz

theorem retractedBaseTwoStepCode_prefix (m z : V) :
    kpair.π₁ (retractedBaseTwoStepCode m z) = m ‘ (kpair.π₁ z) := by
  simp [retractedBaseTwoStepCode]

theorem retractedBaseTwoStepCode_empty_tail (m p : V) :
    retractedBaseTwoStepCode m ⟨p, ∅⟩ₖ = ⟨m ‘ p, ∅⟩ₖ := by
  rw [retractedBaseTwoStepCode_pair, nameAction_empty]

/-- The recoded subcarrier is exactly the bounded two-step carrier over the
preceding suborder, using the specified translated iterand name. -/
theorem retractedBaseTwoStep_eq_translated {P R N T m δ Q : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hQ : IsForcingName P Q) :
    retractedBaseTwoStep P R δ Q N = boundedNameTwoStep N T δ (nameAction m Q) := by
  have hm (p τ : V) (hp : p ∈ N) (hτ : IsForcingName N τ) :
      p ∈ atomicMembership P R τ Q ↔ p ∈ atomicMembership N T τ (nameAction m Q) := by
    simpa only [hr.fixes p hp, nameAction_eq_self_of_fixes_conditions hr.fixes hτ] using
      hr.atomicMembership_nameAction_iff hR he (hτ.mono hr.inclusion) hQ (hr.inclusion p hp)
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hb, hn, hτN⟩ := mem_sep_iff.mp hz
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hb).1
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hn hτN
    obtain ⟨_, hτδ, _, hτQ⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hb
    exact (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr ⟨hn, hτδ, hτN, (hm p τ hn hτN).mp hτQ⟩
  · intro hz
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    obtain ⟨hp, hτδ, hτ, hτQ⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
    apply mem_sep_iff.mpr
    refine ⟨(pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr
      ⟨hr.inclusion p hp, hτδ, hτ.mono hr.inclusion, (hm p τ hp hτ).mpr hτQ⟩, ?_⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hp hτ

theorem retractedBaseTwoStep_order_iff {P R N T m δ Q S z w : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hS : IsForcingName P S)
    (hz : z ∈ retractedBaseTwoStep P R δ Q N) (hw : w ∈ retractedBaseTwoStep P R δ Q N) :
    ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn P R S (retractedBaseTwoStep P R δ Q N) ↔
      ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn N T (nameAction m S) (retractedBaseTwoStep P R δ Q N) := by
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp (mem_sep_iff.mp hz).1).1
  obtain ⟨q, _, σ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp (mem_sep_iff.mp hw).1).1
  have hp : p ∈ N := by simpa using (mem_sep_iff.mp hz).2.1
  have hq : q ∈ N := by simpa using (mem_sep_iff.mp hw).2.1
  have hτ : IsForcingName N τ := by simpa using (mem_sep_iff.mp hz).2.2
  have hσ : IsForcingName N σ := by simpa using (mem_sep_iff.mp hw).2.2
  have hv : ∀ i : Fin 3, IsForcingName P (![S, τ, σ] i) := by
    intro i
    exact Fin.cases hS (fun j ↦ Fin.cases (hτ.mono hr.inclusion)
      (fun k ↦ Fin.cases (hσ.mono hr.inclusion) (fun l ↦ Fin.elim0 l) k) j) i
  have hnames : (fun i : Fin 3 ↦ nameAction m (![S, τ, σ] i)) = ![nameAction m S, τ, σ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases (nameAction_eq_self_of_fixes_conditions hr.fixes hτ)
      (fun k ↦ Fin.cases (nameAction_eq_self_of_fixes_conditions hr.fixes hσ) (fun l ↦ Fin.elim0 l) k) j) i
  have hforce := hr.forcingFormula_nameAction_iff hR hT he boundedPairMemberFormula ![S, τ, σ] hv
    (hr.inclusion p hp)
  rw [hr.fixes p hp, hnames] at hforce
  have hrel := hr.below p (hr.inclusion p hp) q hq
  rw [hr.fixes p hp] at hrel
  rw [pair_mem_nameTwoStepOrderOn, pair_mem_nameTwoStepOrderOn]
  simp only [hz, hw, true_and]
  exact and_congr hrel hforce

theorem retractedBaseTwoStepOrder_eq_translated {P R N T m δ Q S : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S) :
    nameTwoStepOrderOn P R S (retractedBaseTwoStep P R δ Q N) =
      nameTwoStepOrderOn N T (nameAction m S) (boundedNameTwoStep N T δ (nameAction m Q)) := by
  rw [← retractedBaseTwoStep_eq_translated hr hR he hQ]
  apply mem_ext
  intro a
  constructor
  · intro ha
    obtain ⟨z, hz, w, hw, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp ha).1
    exact (retractedBaseTwoStep_order_iff hr hR hT he hS hz hw).mp ha
  · intro ha
    obtain ⟨z, hz, w, hw, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp ha).1
    exact (retractedBaseTwoStep_order_iff hr hR hT he hS hz hw).mpr ha

theorem retractedBaseTwoStepMap_translated_retraction {P R one N T m δ Q S : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) :
    IsForcingRetraction (boundedNameTwoStep N T δ (nameAction m Q))
      (nameTwoStepOrderOn N T (nameAction m S) (boundedNameTwoStep N T δ (nameAction m Q)))
      (boundedNameTwoStep P R δ Q) (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q))
      (retractedBaseTwoStepMap P R δ Q m) := by
  have hh := retractedBaseTwoStepMap_retraction hR ht hδ hP hr.inclusion hr.maps hr.fixes he hI
  rwa [retractedBaseTwoStepOrder_eq_translated hr hR hT he hI.posetName hI.orderName,
    retractedBaseTwoStep_eq_translated hr hR he hI.posetName] at hh

theorem IsForcingRetraction.iterand_nameAction {P R N T m Q S t : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S t) :
    IsForcingIterand N T (nameAction m Q) (nameAction m S) (nameAction m t) := by
  refine ⟨nameAction_isName hr.maps hI.posetName, nameAction_isName hr.maps hI.orderName,
    nameAction_isName hr.maps hI.topName, ?_, ?_⟩
  · intro p hp
    have hv : ∀ i : Fin 2, IsForcingName P (![Q, S] i) := fun i ↦
      Fin.cases hI.posetName (fun j ↦ Fin.cases hI.orderName (fun k ↦ Fin.elim0 k) j) i
    have hh := (hr.forcingFormula_nameAction_iff hR hT he forcingPreorderFormula ![Q, S] hv
      (hr.inclusion p hp)).mp (hI.preorder p (hr.inclusion p hp))
    have hnames : (fun i : Fin 2 ↦ nameAction m (![Q, S] i)) = ![nameAction m Q, nameAction m S] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    rwa [hr.fixes p hp, hnames] at hh
  · intro p hp
    have hv : ∀ i : Fin 3, IsForcingName P (![Q, S, t] i) := fun i ↦
      Fin.cases hI.posetName (fun j ↦ Fin.cases hI.orderName
        (fun k ↦ Fin.cases hI.topName (fun l ↦ Fin.elim0 l) k) j) i
    have hh := (hr.forcingFormula_nameAction_iff hR hT he forcingTopFormula ![Q, S, t] hv
      (hr.inclusion p hp)).mp (hI.top p (hr.inclusion p hp))
    have hnames : (fun i : Fin 3 ↦ nameAction m (![Q, S, t] i)) =
        ![nameAction m Q, nameAction m S, nameAction m t] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    rwa [hr.fixes p hp, hnames] at hh

end ZFVP
