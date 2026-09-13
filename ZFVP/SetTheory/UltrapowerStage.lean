import ZFVP.SetTheory.UltrapowerConstant
import ZFVP.SetTheory.SupercompactMeasure
import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.InternalChoice
import ZFVP.ModelTheory.ConstantStructure

/-! The almost everywhere layer of the internal ultrapower on the
supercompactness side of the import graph. It uses the shared constant-function
helper and retains the stage-specific relations and collapse construction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The two pointwise index sets -/

/-- The index set on which two functions agree. -/
noncomputable def ultraAgree (P f g : V) : V := {p ∈ P ; f ‘ p = g ‘ p}

/-- The index set on which one function's value belongs to the other's. -/
noncomputable def ultraMem (P f g : V) : V := {p ∈ P ; f ‘ p ∈ g ‘ p}

instance ultraAgree_definable : ℒₛₑₜ-function₃[V] ultraAgree := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y P f g ↦ ∀ p, p ∈ Y ↔ p ∈ P ∧ f ‘ p = g ‘ p) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = ultraAgree (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [ultraAgree, mem_sep_iff]

instance ultraMem_definable : ℒₛₑₜ-function₃[V] ultraMem := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y P f g ↦ ∀ p, p ∈ Y ↔ p ∈ P ∧ f ‘ p ∈ g ‘ p) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = ultraMem (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [ultraMem, mem_sep_iff]

@[simp] theorem mem_ultraAgree_iff (P f g p : V) :
    p ∈ ultraAgree P f g ↔ p ∈ P ∧ f ‘ p = g ‘ p := by simp [ultraAgree]

@[simp] theorem mem_ultraMem_iff (P f g p : V) :
    p ∈ ultraMem P f g ↔ p ∈ P ∧ f ‘ p ∈ g ‘ p := by simp [ultraMem]

theorem ultraAgree_subset (P f g : V) : ultraAgree P f g ⊆ P := by
  intro p hp
  exact (mem_ultraAgree_iff P f g p).mp hp |>.1

theorem ultraMem_subset (P f g : V) : ultraMem P f g ⊆ P := by
  intro p hp
  exact (mem_ultraMem_iff P f g p).mp hp |>.1

theorem ultraAgree_self (P f : V) : ultraAgree P f f = P := by
  apply mem_ext
  intro p
  simp [ultraAgree]

/-! ### The two a.e. relations -/

/-- Equality almost everywhere with respect to `U`. -/
def UltraEq (P U f g : V) : Prop := ultraAgree P f g ∈ U

/-- Membership almost everywhere with respect to `U`. -/
def UltraMem (P U f g : V) : Prop := ultraMem P f g ∈ U

instance ultraEq_definable : ℒₛₑₜ-relation₄[V] UltraEq := by
  unfold UltraEq
  definability

instance ultraMem_rel_definable : ℒₛₑₜ-relation₄[V] UltraMem := by
  unfold UltraMem
  definability

variable {P U A X Y f f' g g' k : V}

/-- The index set of a set ultrafilter belongs to it. -/
theorem ultraIndex_mem (h : IsSetUltrafilter P U) : P ∈ U := h.2.1

/-- Exactly one of a subset of the index set and its relative complement is in the
ultrafilter. -/
theorem ultraCompl_mem_iff (h : IsSetUltrafilter P U) (hX : X ⊆ P) :
    relativeComplement P X ∈ U ↔ X ∉ U := by
  constructor
  · intro hc
    exact h.not_mem_of_complement_mem hc
  · intro hXU
    rcases h.dichotomy hX with hin | hout
    · exact (hXU hin).elim
    · exact hout

theorem ultraEq_refl (h : IsSetUltrafilter P U) : UltraEq P U f f := by
  unfold UltraEq
  rw [ultraAgree_self]
  exact ultraIndex_mem h

theorem UltraEq.symm (h : IsSetUltrafilter P U) (hfg : UltraEq P U f g) : UltraEq P U g f := by
  refine h.upward hfg (ultraAgree_subset P g f) ?_
  intro p hp
  obtain ⟨hpP, hv⟩ := (mem_ultraAgree_iff P f g p).mp hp
  exact (mem_ultraAgree_iff P g f p).mpr ⟨hpP, hv.symm⟩

theorem UltraEq.trans (h : IsSetUltrafilter P U) (hfg : UltraEq P U f g) (hgk : UltraEq P U g k) :
    UltraEq P U f k := by
  refine h.upward (h.inter hfg hgk) (ultraAgree_subset P f k) ?_
  intro p hp
  rw [mem_inter_iff, mem_ultraAgree_iff, mem_ultraAgree_iff] at hp
  exact (mem_ultraAgree_iff P f k p).mpr ⟨hp.1.1, hp.1.2.trans hp.2.2⟩

/-- Membership almost everywhere respects equality almost everywhere in both arguments. -/
theorem UltraMem.congr (h : IsSetUltrafilter P U) (hff' : UltraEq P U f f')
    (hgg' : UltraEq P U g g') (hmem : UltraMem P U f g) : UltraMem P U f' g' := by
  refine h.upward (h.inter (h.inter hff' hgg') hmem) (ultraMem_subset P f' g') ?_
  intro p hp
  rw [mem_inter_iff, mem_inter_iff, mem_ultraAgree_iff, mem_ultraAgree_iff,
    mem_ultraMem_iff] at hp
  refine (mem_ultraMem_iff P f' g' p).mpr ⟨hp.2.1, ?_⟩
  rw [← hp.1.1.2, ← hp.1.2.2]
  exact hp.2.2

/-- Almost everywhere, either the values agree or they do not. -/
theorem ultraEq_or_not (h : IsSetUltrafilter P U) :
    UltraEq P U f g ∨ relativeComplement P (ultraAgree P f g) ∈ U :=
  h.dichotomy (ultraAgree_subset P f g)

theorem ultraMem_or_not (h : IsSetUltrafilter P U) :
    UltraMem P U f g ∨ relativeComplement P (ultraMem P f g) ∈ U :=
  h.dichotomy (ultraMem_subset P f g)

/-! ### Constant functions -/

/-- The index set where a constant function's value belongs to `g`'s value. -/
theorem ultraMem_constantGraph_left (P x g : V) :
    ultraMem P (constantGraph P x) g = {p ∈ P ; x ∈ g ‘ p} := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp]
    exact ⟨hp, hv⟩

/-- The index set where `f`'s value belongs to a constant function's value. -/
theorem ultraMem_constantGraph_right (P f y : V) :
    ultraMem P f (constantGraph P y) = {p ∈ P ; f ‘ p ∈ y} := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P y hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P y hp]
    exact ⟨hp, hv⟩

/-- The index set where a constant function agrees with `g`. -/
theorem ultraAgree_constantGraph_left (P x g : V) :
    ultraAgree P (constantGraph P x) g = {p ∈ P ; x = g ‘ p} := by
  apply mem_ext
  intro p
  rw [mem_ultraAgree_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp]
    exact ⟨hp, hv⟩

/-- A constant function agrees with itself everywhere on the index set. -/
theorem ultraAgree_constantGraph_eq (P x : V) :
    ultraAgree P (constantGraph P x) (constantGraph P x) = P :=
  ultraAgree_self P (constantGraph P x)

/-- Constant functions with different values agree nowhere. -/
theorem ultraAgree_constantGraph_ne {P x y : V} (h : x ≠ y) :
    ultraAgree P (constantGraph P x) (constantGraph P y) = (∅ : V) := by
  apply mem_ext
  intro p
  rw [mem_ultraAgree_iff]
  simp only [not_mem_empty, iff_false, not_and]
  intro hp
  rw [value_constantGraph P x hp, value_constantGraph P y hp]
  exact h

/-- If the value of one constant function belongs to the value of another, the pointwise
membership set is the whole index set. -/
theorem ultraMem_constantGraph_mem {P x y : V} (h : x ∈ y) :
    ultraMem P (constantGraph P x) (constantGraph P y) = P := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff]
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    rw [value_constantGraph P x hp, value_constantGraph P y hp]
    exact h

/-- If the value of one constant function does not belong to the value of another, the pointwise
membership set is empty. -/
theorem ultraMem_constantGraph_not_mem {P x y : V} (h : x ∉ y) :
    ultraMem P (constantGraph P x) (constantGraph P y) = (∅ : V) := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff]
  simp only [not_mem_empty, iff_false, not_and]
  intro hp
  rw [value_constantGraph P x hp, value_constantGraph P y hp]
  exact h

/-- One constant function is an a.e. member of another exactly when its value is. -/
theorem ultraMem_constantGraph_iff {P U : V} (hU : IsSetUltrafilter P U) (x y : V) :
    UltraMem P U (constantGraph P x) (constantGraph P y) ↔ x ∈ y := by
  constructor
  · intro hae
    by_contra hnm
    rw [UltraMem, ultraMem_constantGraph_not_mem hnm] at hae
    exact hU.empty_not_mem hae
  · intro hm
    rw [UltraMem, ultraMem_constantGraph_mem hm]
    exact ultraIndex_mem hU

/-- Two constant functions agree almost everywhere exactly when their values are equal. -/
theorem ultraEq_constantGraph_iff {P U : V} (hU : IsSetUltrafilter P U) (x y : V) :
    UltraEq P U (constantGraph P x) (constantGraph P y) ↔ x = y := by
  constructor
  · intro hae
    by_contra hne
    rw [UltraEq, ultraAgree_constantGraph_ne hne] at hae
    exact hU.empty_not_mem hae
  · rintro rfl
    rw [UltraEq, ultraAgree_constantGraph_eq]
    exact ultraIndex_mem hU

/-! ### The a.e. membership relation as an internal set -/

/-- The a.e. membership relation on the functions from `P` into `A`, as an internal set. -/
noncomputable def ultraMemRelation (P U A : V) : V :=
  {q ∈ (A ^ P) ×ˢ (A ^ P) ; UltraMem P U (kpair.π₁ q) (kpair.π₂ q)}

instance ultraMemRelation_definable : ℒₛₑₜ-function₃[V] ultraMemRelation := by
  have hd : ℒₛₑₜ-relation₄[V] (fun R P U A ↦ ∀ q, q ∈ R ↔
      q ∈ (A ^ P) ×ˢ (A ^ P) ∧ UltraMem P U (kpair.π₁ q) (kpair.π₂ q)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = ultraMemRelation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [ultraMemRelation, mem_sep_iff]

theorem pair_mem_ultraMemRelation_iff (P U A f g : V) :
    ⟨f, g⟩ₖ ∈ ultraMemRelation P U A ↔ f ∈ A ^ P ∧ g ∈ A ^ P ∧ UltraMem P U f g := by
  simp [ultraMemRelation, and_assoc]

theorem ultraMemRelation_subset (P U A : V) : ultraMemRelation P U A ⊆ (A ^ P) ×ˢ (A ^ P) := by
  intro q hq
  exact (mem_sep_iff.mp hq).1

/-- The a.e. membership relation of an ultrafilter that is complete for intersections of
`ω`-many of its members is internally well founded: an internal descending chain would give a
single index at which the real membership chain descends forever. -/
theorem ultraMemRelation_wellFounded (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ) :
    IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) := by
  intro B hB hne
  by_contra hcon
  push Not at hcon
  -- The reversed relation, restricted to `B`.
  have hRd : ℒₛₑₜ-predicate (fun q : V ↦ ⟨kpair.π₂ q, kpair.π₁ q⟩ₖ ∈ ultraMemRelation P U A) := by
    definability
  set R' : V := sep (B ×ˢ B) (fun q ↦ ⟨kpair.π₂ q, kpair.π₁ q⟩ₖ ∈ ultraMemRelation P U A) hRd
    with hR'def
  have hpairR' : ∀ x y : V, x ∈ B → y ∈ B →
      ⟨y, x⟩ₖ ∈ ultraMemRelation P U A → ⟨x, y⟩ₖ ∈ R' := by
    intro x y hx hy hxy
    rw [hR'def, mem_sep_iff]
    refine ⟨mem_prod_iff.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
    simpa using hxy
  have hserial : ∀ x ∈ B, ∃ y ∈ B, ⟨x, y⟩ₖ ∈ R' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcon x hx
    exact ⟨y, hy, hpairR' x y hx hy hyx⟩
  obtain ⟨s, hsf, hstep⟩ :=
    dependentChoice_of_internalChoice hAC B R' hne hserial
  -- Each step of the chain gives a set of indices in the ultrafilter.
  have hmem : ∀ n ∈ (ω : V), ultraMem P (s ‘ (succ n)) (s ‘ n) ∈ U := by
    intro n hn
    have h := hstep n hn
    rw [hR'def, mem_sep_iff] at h
    have h2 := h.2
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h2
    exact ((pair_mem_ultraMemRelation_iff P U A (s ‘ (succ n)) (s ‘ n)).mp h2).2.2
  have hF : ℒₛₑₜ-function₁ (fun n : V ↦ ultraMem P (s ‘ (succ n)) (s ‘ n)) := by
    definability
  set g : V := definableGraph (ω : V) (fun n ↦ ultraMem P (s ‘ (succ n)) (s ‘ n)) hF
    with hgdef
  have hgf : g ∈ U ^ (ω : V) :=
    definableGraph_mem_function_of_mapsTo _ _ _ hF hmem
  have hint : indexedIntersection P (ω : V) g ∈ U := hcomp (ω : V) hω g hgf
  obtain ⟨p, hp⟩ := hU.nonempty_of_mem hint
  rw [mem_indexedIntersection_iff] at hp
  have hchain : ∀ n ∈ (ω : V), (s ‘ (succ n)) ‘ p ∈ (s ‘ n) ‘ p := by
    intro n hn
    have h := hp.2 n hn
    rw [hgdef, value_definableGraph _ _ hF hn, mem_ultraMem_iff] at h
    exact h.2
  -- The pointwise values at `p` form a set with no membership-minimal element.
  have hT : ℒₛₑₜ-function₁ (fun n : V ↦ (s ‘ n) ‘ p) := by definability
  set T : V := range (definableGraph (ω : V) (fun n ↦ (s ‘ n) ‘ p) hT) with hTdef
  have hmemT : ∀ t : V, t ∈ T ↔ ∃ n ∈ (ω : V), t = (s ‘ n) ‘ p := by
    intro t
    rw [hTdef, range_definableGraph, repl_spec]
  have hTne : IsNonempty T :=
    ⟨(s ‘ (∅ : V)) ‘ p, (hmemT _).mpr ⟨∅, empty_mem_ω, rfl⟩⟩
  obtain ⟨x, hx, hxmin⟩ := membershipRelation_wellFounded T T (fun _ h ↦ h) hTne
  obtain ⟨n, hn, rfl⟩ := (hmemT x).mp hx
  have hy : (s ‘ (succ n)) ‘ p ∈ T := (hmemT _).mpr ⟨succ n, ω_succ_closed hn, rfl⟩
  exact hxmin _ hy ((pair_mem_membershipRelation T _ _).mpr ⟨hy, hx, hchain n hn⟩)

/-! ### Extensionality -/

/-- At the index `p`, the members of `A` that separate the value of `f` from the value of `g`,
together with the fallback point `a` at the indices where the two values agree. The fallback keeps
the family nonempty at every index, so a single choice function covers the whole index set. -/
noncomputable def ultraDifferenceWitnesses (A a f g p : V) : V :=
  {z ∈ A ; (z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨ (f ‘ p = g ‘ p ∧ z = a)}

theorem mem_ultraDifferenceWitnesses_iff (A a f g p z : V) :
    z ∈ ultraDifferenceWitnesses A a f g p ↔
      z ∈ A ∧ ((z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨ (f ‘ p = g ‘ p ∧ z = a)) :=
  mem_sep_iff

theorem ultraDifferenceWitnesses_definable_one (A a f g : V) :
    ℒₛₑₜ-function₁[V] (ultraDifferenceWitnesses A a f g) := by
  have h : ℒₛₑₜ-relation[V] (fun S p ↦ ∀ z, z ∈ S ↔
      z ∈ A ∧ ((z ∈ f ‘ p ∧ z ∉ g ‘ p) ∨ (z ∈ g ‘ p ∧ z ∉ f ‘ p) ∨
        (f ‘ p = g ‘ p ∧ z = a))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = ultraDifferenceWitnesses A a f g (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [ultraDifferenceWitnesses, mem_sep_iff]

theorem ultraDifferenceWitnesses_subset (A a f g p : V) :
    ultraDifferenceWitnesses A a f g p ⊆ A := by
  intro z hz
  exact ((mem_ultraDifferenceWitnesses_iff A a f g p z).mp hz).1

/-- The family of separating witnesses is nonempty at every index. -/
theorem ultraDifferenceWitnesses_nonempty {P A a f g : V} [IsTransitive A] (ha : a ∈ A)
    (hf : f ∈ A ^ P) (hg : g ∈ A ^ P) {p : V} (hp : p ∈ P) :
    IsNonempty (ultraDifferenceWitnesses A a f g p) := by
  by_cases heq : f ‘ p = g ‘ p
  · exact ⟨⟨a, (mem_ultraDifferenceWitnesses_iff A a f g p a).mpr
      ⟨ha, Or.inr (Or.inr ⟨heq, rfl⟩)⟩⟩⟩
  · have hex : ∃ z, ¬(z ∈ f ‘ p ↔ z ∈ g ‘ p) := by
      by_contra hc
      exact heq (mem_ext fun z ↦ not_not.mp (fun hz ↦ hc ⟨z, hz⟩))
    obtain ⟨z, hz⟩ := hex
    by_cases hzf : z ∈ f ‘ p
    · have hzg : z ∉ g ‘ p := fun hzg ↦ hz ⟨fun _ ↦ hzg, fun _ ↦ hzf⟩
      have hzA : z ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hzf (function_value_mem hf hp)
      exact ⟨⟨z, (mem_ultraDifferenceWitnesses_iff A a f g p z).mpr ⟨hzA, Or.inl ⟨hzf, hzg⟩⟩⟩⟩
    · have hzg : z ∈ g ‘ p := by
        by_contra hc
        exact hz ⟨fun hh ↦ absurd hh hzf, fun hh ↦ absurd hh hc⟩
      have hzA : z ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hzg (function_value_mem hg hp)
      exact ⟨⟨z, (mem_ultraDifferenceWitnesses_iff A a f g p z).mpr
        ⟨hzA, Or.inr (Or.inl ⟨hzg, hzf⟩)⟩⟩⟩

/-- A function whose domain is `P` and whose values lie in `A` is a member of `A ^ P`. -/
theorem mem_function_of_domain_values {P A k : V} (hk : IsFunction k) (hd : domain k = P)
    (hval : ∀ p ∈ P, k ‘ p ∈ A) : k ∈ A ^ P := by
  have : IsFunction k := hk
  obtain ⟨X', Y', hk'⟩ := hk.mem_func
  rw [mem_function_iff]
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨x, -, y, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hk' q hq)
    have hx : x ∈ P := hd ▸ mem_domain_of_kpair_mem hq
    have hy : y = k ‘ x := (value_eq_of_kpair_mem hq).symm
    exact kpair_mem_iff.mpr ⟨hx, hy ▸ hval x hx⟩
  · intro x hx
    rw [← hd] at hx
    exact ⟨k ‘ x, kpair_value_mem hx, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩

/-- Two functions into a transitive set with the same a.e. members are a.e. equal. This is
extensionality for the ultrapower, and it is where internal choice enters: a witness has to be
picked at every index where the two values differ. -/
theorem ultraEq_of_ultraMem_iff (hAC : InternalChoice V) {P U A f g : V} [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hA : IsNonempty A) (hf : f ∈ A ^ P) (hg : g ∈ A ^ P)
    (h : ∀ k, k ∈ A ^ P → (UltraMem P U k f ↔ UltraMem P U k g)) :
    UltraEq P U f g := by
  by_contra hnot
  have hD : relativeComplement P (ultraAgree P f g) ∈ U :=
    (ultraCompl_mem_iff hU (ultraAgree_subset P f g)).mpr hnot
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨k, hkfun, hkdom, hkval⟩ :=
    choice_for_definable_family hAC P (ultraDifferenceWitnesses A a f g)
      (ultraDifferenceWitnesses_definable_one A a f g)
      (fun p hp ↦ ultraDifferenceWitnesses_nonempty ha hf hg hp)
  have hkA : k ∈ A ^ P :=
    mem_function_of_domain_values hkfun hkdom
      (fun p hp ↦ ultraDifferenceWitnesses_subset A a f g p _ (hkval p hp))
  -- On the complement of the agreement set the two values differ, so the chosen witness lies in
  -- exactly one of them.
  have hsplit : ∀ p ∈ relativeComplement P (ultraAgree P f g),
      p ∈ P ∧ ((k ‘ p ∈ f ‘ p ∧ k ‘ p ∉ g ‘ p) ∨ (k ‘ p ∈ g ‘ p ∧ k ‘ p ∉ f ‘ p)) := by
    intro p hp
    rw [mem_relativeComplement_iff] at hp
    obtain ⟨hpP, hpa⟩ := hp
    have hne : f ‘ p ≠ g ‘ p := fun he ↦ hpa ((mem_ultraAgree_iff P f g p).mpr ⟨hpP, he⟩)
    have hw := (mem_ultraDifferenceWitnesses_iff A a f g p _).mp (hkval p hpP)
    refine ⟨hpP, ?_⟩
    rcases hw.2 with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd h3.1 hne
  set D₁ : V := ultraMem (relativeComplement P (ultraAgree P f g)) k f with hD₁
  have hD₁sub : D₁ ⊆ relativeComplement P (ultraAgree P f g) :=
    ultraMem_subset _ k f
  have hD₁P : D₁ ⊆ P := fun p hp ↦ (hsplit p (hD₁sub p hp)).1
  rcases hU.dichotomy hD₁P with hin | hout
  · -- The witness is a.e. in `f`, hence a.e. in `g`, but it is nowhere in `g` on `D₁`.
    have hmemf : UltraMem P U k f := by
      refine hU.upward hin (ultraMem_subset P k f) ?_
      intro p hp
      have hp' := (mem_ultraMem_iff _ k f p).mp hp
      exact (mem_ultraMem_iff P k f p).mpr ⟨(hsplit p hp'.1).1, hp'.2⟩
    have hmemg : UltraMem P U k g := (h k hkA).mp hmemf
    obtain ⟨p, hp⟩ := hU.nonempty_of_mem (hU.inter hin hmemg)
    rw [mem_inter_iff] at hp
    have hp1 := (mem_ultraMem_iff _ k f p).mp hp.1
    have hp2 := (mem_ultraMem_iff P k g p).mp hp.2
    rcases (hsplit p hp1.1).2 with h1 | h2
    · exact h1.2 hp2.2
    · exact h2.2 hp1.2
  · -- Off `D₁` the witness is a.e. in `g`, hence a.e. in `f`, contradicting the split again.
    have hE : relativeComplement P (ultraAgree P f g) ∩ relativeComplement P D₁ ∈ U :=
      hU.inter hD hout
    have hEg : ∀ p ∈ relativeComplement P (ultraAgree P f g) ∩ relativeComplement P D₁,
        p ∈ P ∧ k ‘ p ∈ g ‘ p ∧ k ‘ p ∉ f ‘ p := by
      intro p hp
      rw [mem_inter_iff] at hp
      obtain ⟨hpD, hpc⟩ := hp
      rw [mem_relativeComplement_iff] at hpc
      obtain ⟨-, hpD₁⟩ := hpc
      obtain ⟨hpP, hcase⟩ := hsplit p hpD
      rcases hcase with h1 | h2
      · exact absurd ((mem_ultraMem_iff _ k f p).mpr ⟨hpD, h1.1⟩) hpD₁
      · exact ⟨hpP, h2.1, h2.2⟩
    have hmemg : UltraMem P U k g := by
      refine hU.upward hE (ultraMem_subset P k g) ?_
      intro p hp
      obtain ⟨hpP, hpg, -⟩ := hEg p hp
      exact (mem_ultraMem_iff P k g p).mpr ⟨hpP, hpg⟩
    have hmemf : UltraMem P U k f := (h k hkA).mpr hmemg
    obtain ⟨p, hp⟩ := hU.nonempty_of_mem (hU.inter hE hmemf)
    rw [mem_inter_iff] at hp
    obtain ⟨-, -, hpf⟩ := hEg p hp.1
    exact hpf ((mem_ultraMem_iff P k f p).mp hp.2).2

end ZFVP
