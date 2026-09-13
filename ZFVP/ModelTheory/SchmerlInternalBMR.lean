import ZFVP.ModelTheory.SchmerlInternalFiniteUltrafilter
import ZFVP.SetTheory.RegularUnions

/-! The uniform-ultrafilter argument for internal tree specialization. All
tuple families, choice functions, and unions are sets of the ground model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internal_countable_union (hAC : InternalChoice V) {I : V}
    (hI : IsInternallyCountable I) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hsmall : ∀ i ∈ I, IsInternallyCountable (F i)) :
    IsInternallyCountable (⋃ˢ repl F hF I) := by
  let g := definableGraph I F hF
  have : IsFunction g := definableGraph_isFunction I F hF
  have hr : range g = repl F hF I := range_definableGraph I F hF
  rw [← hr]
  have hle := sUnion_range_cardLE_prod hAC (domain_definableGraph I F hF)
    (fun i hi ↦ by
      change g ‘ i ≤# (ω : V)
      rw [show g ‘ i = F i from value_definableGraph I F hF hi]
      exact hsmall i hi)
  exact (hle.trans (prod_cardLE_prod hI (CardLE.refl (ω : V)))).trans omega_prod_cardLE_omega

theorem internal_fiber_definable (A : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-function₁ (fun i ↦ {a ∈ A ; R i a}) := by
  have h : ℒₛₑₜ-relation[V] (fun X i ↦ ∀ a, a ∈ X ↔ a ∈ A ∧ R i a) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_sep_iff]
  rfl

theorem internal_tuple_value_mem {D A n t a i : V}
    (ht : t ∈ (D ^ n) ^ A) (ha : a ∈ A) (hi : i ∈ n) : (t ‘ a) ‘ i ∈ D :=
  function_value_mem (function_value_mem ht ha) hi

set_option maxHeartbeats 800000 in
theorem internal_bounded_occurrences_countable (hAC : InternalChoice V)
    {D S A n t : V} (ht : t ∈ (D ^ n) ^ A)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (hsmall : ∀ x ∈ D, IsInternallyCountable {a ∈ A ; ∃ i ∈ n, (t ‘ a) ‘ i = x})
    {x : V} (hx : x ∈ D) :
    IsInternallyCountable {a ∈ A ; ∃ i ∈ n, ⟨(t ‘ a) ‘ i, x⟩ₖ ∈ S} := by
  let B : V := {y ∈ D ; ⟨y, x⟩ₖ ∈ S}
  have hB : IsInternallyCountable B := by
    apply hchains B sep_subset
    intro y hy z hz
    obtain ⟨hyD, hyx⟩ := mem_sep_iff.mp hy
    obtain ⟨hzD, hzx⟩ := mem_sep_iff.mp hz
    exact hbelow y hyD z hzD x hx hyx hzx
  let F : V → V := fun y ↦ {a ∈ A ; ∃ i ∈ n, (t ‘ a) ‘ i = y}
  have hF : ℒₛₑₜ-function₁ F := internal_fiber_definable A _ (by definability)
  apply internallyCountable_subset (internal_countable_union hAC hB F hF
    (fun y hy ↦ hsmall y (mem_sep_iff.mp hy).1))
  intro a ha
  obtain ⟨haA, i, hi, hix⟩ := mem_sep_iff.mp ha
  exact mem_sUnion_iff.mpr ⟨F ((t ‘ a) ‘ i), (repl_spec hF).mpr
    ⟨(t ‘ a) ‘ i, mem_sep_iff.mpr ⟨internal_tuple_value_mem ht haA hi, hix⟩, rfl⟩,
    mem_sep_iff.mpr ⟨haA, i, hi, rfl⟩⟩

set_option maxHeartbeats 800000 in
theorem internal_reverse_comparisons_countable (hAC : InternalChoice V)
    {D S A n t : V} (hn : n ∈ (ω : V)) (ht : t ∈ (D ^ n) ^ A)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (hsmall : ∀ x ∈ D, IsInternallyCountable {a ∈ A ; ∃ i ∈ n, (t ‘ a) ‘ i = x})
    {a : V} (ha : a ∈ A) :
    IsInternallyCountable {b ∈ A ; ∃ i ∈ n, ∃ j ∈ n,
      ⟨(t ‘ b) ‘ j, (t ‘ a) ‘ i⟩ₖ ∈ S} := by
  let F : V → V := fun i ↦ {b ∈ A ; ∃ j ∈ n, ⟨(t ‘ b) ‘ j, (t ‘ a) ‘ i⟩ₖ ∈ S}
  have hF : ℒₛₑₜ-function₁ F := internal_fiber_definable A _ (by definability)
  have hnC : IsInternallyCountable n := internallyCountable_of_finite
    (internallyFinite_of_cardLE_natural hn (CardLE.refl n))
  apply internallyCountable_subset (internal_countable_union hAC hnC F hF
    (fun i hi ↦ internal_bounded_occurrences_countable hAC ht hbelow hchains hsmall
      (internal_tuple_value_mem ht ha hi)))
  intro b hb
  obtain ⟨hbA, i, hi, j, hj, hij⟩ := mem_sep_iff.mp hb
  exact mem_sUnion_iff.mpr ⟨F i, (repl_spec hF).mpr ⟨i, hi, rfl⟩,
    mem_sep_iff.mpr ⟨hbA, j, hj, hij⟩⟩

noncomputable def internalUpperFiber (A S t a i j : V) : V :=
  {b ∈ A ; ⟨(t ‘ a) ‘ i, (t ‘ b) ‘ j⟩ₖ ∈ S}

instance internalUpperFiber_definable (A S t : V) :
    ℒₛₑₜ-function₃[V] (internalUpperFiber A S t) := by
  have h : ℒₛₑₜ-relation₄[V] (fun X a i j ↦ ∀ b,
      b ∈ X ↔ b ∈ A ∧ ⟨(t ‘ a) ‘ i, (t ‘ b) ‘ j⟩ₖ ∈ S) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalUpperFiber, mem_sep_iff]
  rfl

set_option maxHeartbeats 1600000 in
/-- The sparse-tuple step of the specialization proof, inside the ZF model.
The hypotheses quantify over internal sets and internal tuples only. -/
theorem internal_countable_of_sparse_cross_comparability (hAC : InternalChoice V)
    {D S A n t : V} (hn : n ∈ (ω : V)) (ht : t ∈ (D ^ n) ^ A)
    (_href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (hsmall : ∀ x ∈ D, IsInternallyCountable {a ∈ A ; ∃ i ∈ n, (t ‘ a) ‘ i = x})
    (hcross : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ i ∈ n, ∃ j ∈ n,
      ⟨(t ‘ a) ‘ i, (t ‘ b) ‘ j⟩ₖ ∈ S ∨ ⟨(t ‘ b) ‘ j, (t ‘ a) ‘ i⟩ₖ ∈ S) :
    IsInternallyCountable A := by
  classical
  by_contra hunc
  obtain ⟨U, hU, hUc⟩ := exists_internal_cocountable_ultrafilter hunc
    (wellOrderable_of_internalChoice hAC (℘ A))
  have hnF : IsInternallyFinite n := internallyFinite_of_cardLE_natural hn (CardLE.refl n)
  have hnC : IsInternallyCountable n := internallyCountable_of_finite hnF
  have hchoice (a : V) (ha : a ∈ A) :
      ∃ i ∈ n, ∃ j ∈ n, internalUpperFiber A S t a i j ∈ U := by
    let B : V := {b ∈ A ; ∃ i ∈ n, ∃ j ∈ n,
      ⟨(t ‘ b) ‘ j, (t ‘ a) ‘ i⟩ₖ ∈ S}
    have hBC : IsInternallyCountable B :=
      internal_reverse_comparisons_countable hAC hn ht hbelow hchains hsmall ha
    let Y := relativeComplement A (insert a B)
    have hYU : Y ∈ U := hUc _ (fun b hb ↦ by
      rcases mem_insert.mp hb with rfl | hb
      · exact ha
      · exact (mem_sep_iff.mp hb).1) (internallyCountable_insert hBC a)
    let F : V → V := fun i ↦ {b ∈ A ; ∃ j ∈ n, ⟨(t ‘ a) ‘ i, (t ‘ b) ‘ j⟩ₖ ∈ S}
    have hF : ℒₛₑₜ-function₁ F := internal_fiber_definable A _ (by definability)
    have hcover : ∀ b ∈ Y, ∃ i ∈ n, b ∈ F i := by
      intro b hb
      obtain ⟨hbA, hbBad⟩ := (mem_relativeComplement_iff _ _ _).mp hb
      have hab : a ≠ b := fun hab ↦ hbBad (mem_insert.mpr (Or.inl hab.symm))
      obtain ⟨i, hi, j, hj, hij | hji⟩ := hcross a ha b hbA hab
      · exact ⟨i, hi, mem_sep_iff.mpr ⟨hbA, j, hj, hij⟩⟩
      · exact False.elim (hbBad (mem_insert.mpr
          (Or.inr (mem_sep_iff.mpr ⟨hbA, i, hi, j, hj, hji⟩))))
    obtain ⟨i, hi, hiU⟩ := ultrafilter_finite_cover hU hnF hYU F hF
      (fun _ _ ↦ sep_subset) hcover
    have hG : ℒₛₑₜ-function₁ (internalUpperFiber A S t a i) := by definability
    obtain ⟨j, hj, hjU⟩ := ultrafilter_finite_cover hU hnF hiU
      (internalUpperFiber A S t a i) hG (fun _ _ ↦ sep_subset) (by
        intro b hb
        obtain ⟨hbA, j, hj, hij⟩ := mem_sep_iff.mp hb
        exact ⟨j, hj, mem_sep_iff.mpr ⟨hbA, hij⟩⟩)
    exact ⟨i, hi, j, hj, hjU⟩
  let Choices : V → V := fun a ↦ {q ∈ n ×ˢ n ;
    internalUpperFiber A S t a (kpair.π₁ q) (kpair.π₂ q) ∈ U}
  have hChoices : ℒₛₑₜ-function₁ Choices := internal_fiber_definable (n ×ˢ n) _ (by definability)
  have hne : ∀ a ∈ A, IsNonempty (Choices a) := by
    intro a ha
    obtain ⟨i, hi, j, hj, hUij⟩ := hchoice a ha
    refine ⟨⟨⟨i, j⟩ₖ, mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hi, hj⟩, ?_⟩⟩⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hUij
  obtain ⟨g, _, _, hg⟩ := choice_for_definable_family hAC A Choices hChoices hne
  let left : V → V := fun a ↦ kpair.π₁ (g ‘ a)
  let right : V → V := fun a ↦ kpair.π₂ (g ‘ a)
  let node : V → V := fun a ↦ (t ‘ a) ‘ (left a)
  have hg₁ (a : V) (ha : a ∈ A) : left a ∈ n ∧ right a ∈ n := by
    obtain ⟨hprod, _⟩ := mem_sep_iff.mp (hg a ha)
    obtain ⟨i, hi, j, hj, he⟩ := mem_prod_iff.mp hprod
    change kpair.π₁ (g ‘ a) ∈ n ∧ kpair.π₂ (g ‘ a) ∈ n
    rw [he]
    simpa only [left, right, kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hi hj
  have hg₂ (a : V) (ha : a ∈ A) : internalUpperFiber A S t a (left a) (right a) ∈ U :=
    (mem_sep_iff.mp (hg a ha)).2
  have hnode (a : V) (ha : a ∈ A) : node a ∈ D :=
    internal_tuple_value_mem ht ha (hg₁ a ha).1
  let C : V → V := fun j ↦ {x ∈ D ; ∃ a ∈ A, right a = j ∧ node a = x}
  have hC : ℒₛₑₜ-function₁ C := by
    apply internal_fiber_definable D
    dsimp only [right, node, left]
    definability
  have hCC (j : V) (_hj : j ∈ n) : IsInternallyCountable (C j) := by
    apply hchains (C j) sep_subset
    intro x hx y hy
    obtain ⟨hxD, a, ha, haj, hax⟩ := mem_sep_iff.mp hx
    obtain ⟨hyD, b, hb, hbj, hby⟩ := mem_sep_iff.mp hy
    obtain ⟨c, hc⟩ := hU.nonempty_of_mem (hU.inter (hg₂ a ha) (hg₂ b hb))
    obtain ⟨hca, hcb⟩ := mem_inter_iff.mp hc
    obtain ⟨hcA, hac⟩ := mem_sep_iff.mp hca
    have hbc := (mem_sep_iff.mp hcb).2
    change ⟨node a, (t ‘ c) ‘ (right a)⟩ₖ ∈ S at hac
    change ⟨node b, (t ‘ c) ‘ (right b)⟩ₖ ∈ S at hbc
    rw [haj, hax] at hac
    rw [hbj, hby] at hbc
    have hjn : j ∈ n := haj ▸ (hg₁ a ha).2
    exact hbelow x hxD y hyD ((t ‘ c) ‘ j) (internal_tuple_value_mem ht hcA hjn) hac hbc
  let E : V := {x ∈ D ; ∃ a ∈ A, node a = x}
  have hEC : IsInternallyCountable E := by
    apply internallyCountable_subset (internal_countable_union hAC hnC C hC hCC)
    intro x hx
    obtain ⟨hxD, a, ha, hax⟩ := mem_sep_iff.mp hx
    exact mem_sUnion_iff.mpr ⟨C (right a), (repl_spec hC).mpr
      ⟨right a, (hg₁ a ha).2, rfl⟩, mem_sep_iff.mpr ⟨hxD, a, ha, rfl, hax⟩⟩
  let Occ : V → V := fun x ↦ {a ∈ A ; ∃ i ∈ n, (t ‘ a) ‘ i = x}
  have hOcc : ℒₛₑₜ-function₁ Occ := internal_fiber_definable A _ (by definability)
  apply hunc
  apply internallyCountable_subset (internal_countable_union hAC hEC Occ hOcc
    (fun x hx ↦ hsmall x (mem_sep_iff.mp hx).1))
  intro a ha
  exact mem_sUnion_iff.mpr ⟨Occ (node a), (repl_spec hOcc).mpr
    ⟨node a, mem_sep_iff.mpr ⟨hnode a ha, a, ha, rfl⟩, rfl⟩,
    mem_sep_iff.mpr ⟨ha, left a, (hg₁ a ha).1, rfl⟩⟩

end ZFVP.Schmerl
