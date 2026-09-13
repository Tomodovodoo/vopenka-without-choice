import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.BooleanCompletionValues
import ZFVP.ModelTheory.LevyConeAlgebraProperties

/-! Gluing an isomorphism of two cones of the Boolean completion out of isomorphisms of the
pieces of two matched partitions.

A cone partition of a nonzero condition `a` is a function `A` on an index set `I` whose values
are nonzero conditions below `a`, pairwise disjoint, with regular join `a`. Given cone partitions
`A` of `a` and `B` of `b` over the same index set and a function `F` on `I` whose value at `i` is
an isomorphism of the cone below `A ‘ i` onto the cone below `B ‘ i`, the map

  `x ↦ regularJoin P R { (F ‘ i) ‘ (x ∩ A ‘ i) : i ∈ I }`

is an isomorphism of the cone below `a` onto the cone below `b`. Its inverse is the same
construction for the converse family.

The empty pieces need no separate treatment: `∅` is not a condition, so it is outside the domain
of every `F ‘ i`, and the repository convention makes the value there `∅`, which contributes
nothing to a regular join. This is what `glueImage_value_empty` records.

The last theorem adds equivariance for a set `D` of regular sets: if each piece map commutes with
meeting a `d ∈ D`, so does the glued map. This needs one clause beyond the piecewise commutation,
`hDpiece` below; see the docstring of `exists_coneIsomorphism_of_conePartitions_equivariant`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Small set facts -/

theorem glue_inter_eq_left {x a : V} (h : x ⊆ a) : x ∩ a = x := by
  apply mem_ext
  intro z
  simp only [mem_inter_iff]
  exact ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, h z hz⟩⟩

theorem glue_inter_right_comm (x y z : V) : (x ∩ y) ∩ z = (x ∩ z) ∩ y := by
  apply mem_ext
  intro w
  simp only [mem_inter_iff]
  tauto

theorem glue_inter_comm (x y : V) : x ∩ y = y ∩ x := by
  apply mem_ext
  intro w
  simp only [mem_inter_iff]
  tauto

theorem glue_inter_assoc (x y z : V) : (x ∩ y) ∩ z = x ∩ (y ∩ z) := by
  apply mem_ext
  intro w
  simp only [mem_inter_iff]
  tauto

theorem glue_eq_empty_of_forall {x : V} (h : ∀ z, z ∉ x) : x = (∅ : V) := by
  apply mem_ext
  intro z
  simp only [not_mem_empty, iff_false]
  exact h z

theorem glue_exists_mem_of_ne_empty {x : V} (h : x ≠ (∅ : V)) : ∃ z, z ∈ x := by
  by_contra hc
  exact h (glue_eq_empty_of_forall (fun z hz ↦ hc ⟨z, hz⟩))

/-- `∅` is not a condition of the completion, so it lies in no cone. -/
theorem empty_not_mem_booleanConditions {P R : V} : (∅ : V) ∉ booleanConditions P R := by
  intro h
  obtain ⟨-, p, hp⟩ := (mem_booleanConditions_iff P R (∅ : V)).mp h
  exact not_mem_empty hp

theorem glue_regularJoin_definable (P R : V) : ℒₛₑₜ-function₁[V] (regularJoin P R) := by
  have h : ℒₛₑₜ-relation (fun J X : V ↦ ∀ p, p ∈ J ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ ⋃ˢ X, ⟨r, q⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = regularJoin P R (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_regularJoin_iff, mem_sUnion_iff]

/-! ### Cone partitions -/

/-- `A` is a cone partition of `a` over `I`: a function on `I` whose values are nonzero
conditions below `a`, pairwise disjoint, with regular join `a`. -/
def IsConePartition (P R a I A : V) : Prop :=
  IsFunction A ∧ domain A = I ∧
  (∀ i, i ∈ I → A ‘ i ∈ booleanConditions P R) ∧
  (∀ i, i ∈ I → A ‘ i ⊆ a) ∧
  (∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → (A ‘ i) ∩ (A ‘ j) = (∅ : V)) ∧
  regularJoin P R (range A) = a

theorem IsConePartition.value_mem_range {P R a I A i : V} (hA : IsConePartition P R a I A)
    (hi : i ∈ I) : A ‘ i ∈ range A := by
  have : IsFunction A := hA.1
  exact mem_range_of_kpair_mem (kpair_value_mem (hA.2.1 ▸ hi))

theorem IsConePartition.exists_index {P R a I A C : V} (hA : IsConePartition P R a I A)
    (hC : C ∈ range A) : ∃ i, i ∈ I ∧ C = A ‘ i := by
  have : IsFunction A := hA.1
  obtain ⟨i, hi⟩ := mem_range_iff.mp hC
  exact ⟨i, hA.2.1 ▸ mem_domain_of_kpair_mem hi, (value_eq_of_kpair_mem hi).symm⟩

theorem IsConePartition.range_subset_poset {P R a I A C : V} (hA : IsConePartition P R a I A)
    (hC : C ∈ range A) : C ⊆ P := by
  obtain ⟨i, hi, rfl⟩ := hA.exists_index hC
  exact (booleanConditions_regular (hA.2.2.1 i hi)).1

/-- The pieces of `x` along the partition, indexed by `I`. -/
theorem IsConePartition.repl_range_eq {P R a I A x : V} (hA : IsConePartition P R a I A) :
    repl (fun C ↦ x ∩ C) (by definability) (range A)
      = repl (fun i ↦ x ∩ A ‘ i) (by definability) I := by
  apply mem_ext
  intro w
  simp only [repl_spec]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hA.exists_index hC
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨A ‘ i, hA.value_mem_range hi, rfl⟩

/-- A regular subset of `a` is the regular join of its pieces along the partition. -/
theorem IsConePartition.regularJoin_pieces {P R a I A x : V} (hR : IsForcingPreorder P R)
    (hA : IsConePartition P R a I A) (hx : IsForcingRegular P R x) (hxa : x ⊆ a) :
    regularJoin P R (repl (fun i ↦ x ∩ A ‘ i) (by definability) I) = x := by
  have h := inter_regularJoin (X := range A) hR hx (fun C hC ↦ hA.range_subset_poset hC)
  rw [hA.2.2.2.2.2, glue_inter_eq_left hxa, hA.repl_range_eq] at h
  exact h.symm

/-- Two regular subsets of `b` with the same pieces along a cone partition of `b` are equal. -/
theorem IsConePartition.eq_of_pieces_eq {P R b I B y z : V} (hR : IsForcingPreorder P R)
    (hB : IsConePartition P R b I B) (hy : IsForcingRegular P R y) (hyb : y ⊆ b)
    (hz : IsForcingRegular P R z) (hzb : z ⊆ b)
    (h : ∀ i, i ∈ I → y ∩ B ‘ i = z ∩ B ‘ i) : y = z := by
  have hpy := hB.regularJoin_pieces hR hy hyb
  have hpz := hB.regularJoin_pieces hR hz hzb
  have he : repl (fun i ↦ y ∩ B ‘ i) (by definability) I
      = repl (fun i ↦ z ∩ B ‘ i) (by definability) I := by
    apply mem_ext
    intro w
    simp only [repl_spec]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, h i hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (h i hi).symm⟩
  rw [← hpy, ← hpz, he]

/-! ### The glue map -/

/-- The set of images of the pieces of `x`. -/
noncomputable def glueImage (I A F x : V) : V :=
  repl (fun i ↦ (F ‘ i) ‘ (x ∩ A ‘ i)) (by definability) I

theorem mem_glueImage_iff (I A F x w : V) :
    w ∈ glueImage I A F x ↔ ∃ i, i ∈ I ∧ w = (F ‘ i) ‘ (x ∩ A ‘ i) := by
  simp only [glueImage, repl_spec]

theorem glueImage_definable (I A F : V) : ℒₛₑₜ-function₁[V] (glueImage I A F) := by
  have h : ℒₛₑₜ-relation (fun C x : V ↦ ∀ w, w ∈ C ↔
      ∃ i, i ∈ I ∧ w = (F ‘ i) ‘ (x ∩ A ‘ i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = glueImage I A F (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_glueImage_iff]

/-- The glued value of `x`. -/
noncomputable def glueValue (P R I A F x : V) : V := regularJoin P R (glueImage I A F x)

theorem glueValue_definable (P R I A F : V) : ℒₛₑₜ-function₁[V] (glueValue P R I A F) := by
  have h1 := glue_regularJoin_definable (V := V) P R
  have h2 := glueImage_definable (V := V) I A F
  unfold glueValue
  definability

/-- The converse family of a family of isomorphisms. -/
noncomputable def conePartitionInverse (I F : V) : V :=
  definableGraph I (fun i ↦ converseGraph (F ‘ i)) (by definability)

theorem conePartitionInverse_value {I F i : V} (hi : i ∈ I) :
    (conePartitionInverse I F) ‘ i = converseGraph (F ‘ i) :=
  value_definableGraph _ _ _ hi


/-! ### Cones of the completion -/

/-- The order of the cone of `c`. -/
noncomputable def boolConeOrder (P R c : V) : V :=
  restrictedOrder (booleanOrder P R) (boolCone P R c)

theorem mem_boolCone_sub_iff {P R c z : V} (hc : c ∈ booleanConditions P R) :
    z ∈ boolCone P R c ↔ z ∈ booleanConditions P R ∧ z ⊆ c :=
  mem_forcingCone_booleanOrder_iff hc

theorem kpair_mem_boolConeOrder_iff {P R c u v : V} (hc : c ∈ booleanConditions P R) :
    (⟨u, v⟩ₖ : V) ∈ boolConeOrder P R c ↔
      (u ∈ booleanConditions P R ∧ u ⊆ c) ∧ (v ∈ booleanConditions P R ∧ v ⊆ c) ∧ u ⊆ v :=
  kpair_mem_coneOrder_iff hc

theorem boolCone_subset (P R c : V) : boolCone P R c ⊆ booleanConditions P R :=
  forcingCone_subset _ _ _

theorem empty_not_mem_boolCone {P R c : V} : (∅ : V) ∉ boolCone P R c :=
  fun h ↦ empty_not_mem_booleanConditions (boolCone_subset P R c (∅ : V) h)

/-- A map of cones takes `∅`, which is not a condition, to `∅`. -/
theorem glue_value_empty {P R c e f : V} (hf : f ∈ (boolCone P R e) ^ (boolCone P R c)) :
    f ‘ (∅ : V) = (∅ : V) :=
  value_eq_empty_of_not_mem_domain (by
    rw [domain_eq_of_mem_function hf]
    exact empty_not_mem_boolCone)

/-- A cone is the range of an isomorphism onto it. -/
theorem glue_exists_preimage {P R c e f y : V}
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f) (hy : y ∈ boolCone P R e) :
    ∃ u, u ∈ boolCone P R c ∧ f ‘ u = y := by
  have : IsFunction f := IsFunction.of_mem hf.1
  obtain ⟨u, hu⟩ := mem_range_iff.mp (hf.2.2.1 ▸ hy)
  exact ⟨u, (domain_eq_of_mem_function hf.1) ▸ mem_domain_of_kpair_mem hu,
    value_eq_of_kpair_mem hu⟩

/-! ### Regular joins with empty members -/

theorem glue_sUnion_eq_empty {X : V} (h : ∀ C, C ∈ X → C = (∅ : V)) : ⋃ˢ X = (∅ : V) := by
  apply glue_eq_empty_of_forall
  intro z hz
  obtain ⟨C, hC, hzC⟩ := mem_sUnion_iff.mp hz
  rw [h C hC] at hzC
  exact not_mem_empty hzC

theorem glue_regularJoin_eq_empty {P R X : V} (hR : IsForcingPreorder P R)
    (h : ∀ C, C ∈ X → C = (∅ : V)) : regularJoin P R X = (∅ : V) := by
  have h1 : regularJoin P R X = regularJoin P R (∅ : V) := by
    unfold regularJoin
    rw [glue_sUnion_eq_empty h, glue_sUnion_eq_empty (fun C hC ↦ absurd hC not_mem_empty)]
  rw [h1, regularJoin_empty hR]

/-- A regular join with a largest member is that member. -/
theorem glue_regularJoin_eq_of_mem {P R X C : V} (hR : IsForcingPreorder P R)
    (hsub : ∀ D, D ∈ X → D ⊆ C) (hCX : C ∈ X) (hC : IsForcingRegular P R C) :
    regularJoin P R X = C :=
  SetTheory.subset_antisymm (regularJoin_subset hR hsub hC) (subset_regularJoin hR hCX hC)

/-! ### The pieces of the glue map -/

section Glue

variable {P R a b I A B F G x : V}

theorem glue_piece_mem_cone (hA : IsConePartition P R a I A) {i : V} (hi : i ∈ I)
    (hx : IsForcingRegular P R x) (hne : x ∩ A ‘ i ≠ (∅ : V)) :
    x ∩ A ‘ i ∈ boolCone P R (A ‘ i) := by
  refine (mem_boolCone_sub_iff (hA.2.2.1 i hi)).mpr ⟨?_, fun z hz ↦ (mem_inter_iff.mp hz).2⟩
  exact (mem_booleanConditions_iff _ _ _).mpr
    ⟨forcingRegular_inter hx (booleanConditions_regular (hA.2.2.1 i hi)),
      glue_exists_mem_of_ne_empty hne⟩

theorem glue_piece_value_mem (hA : IsConePartition P R a I A)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    {i : V} (hi : i ∈ I) (hx : IsForcingRegular P R x) (hne : x ∩ A ‘ i ≠ (∅ : V)) :
    (F ‘ i) ‘ (x ∩ A ‘ i) ∈ boolCone P R (B ‘ i) :=
  function_value_mem (hFiso i hi).1 (glue_piece_mem_cone hA hi hx hne)

theorem glue_piece_value_subset (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    {i : V} (hi : i ∈ I) (hx : IsForcingRegular P R x) :
    (F ‘ i) ‘ (x ∩ A ‘ i) ⊆ B ‘ i := by
  by_cases hne : x ∩ A ‘ i = (∅ : V)
  · rw [hne, glue_value_empty (hFiso i hi).1]
    exact empty_subset _
  · exact ((mem_boolCone_sub_iff (hB.2.2.1 i hi)).mp
      (glue_piece_value_mem hA hFiso hi hx hne)).2

theorem glueImage_subset_poset (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : IsForcingRegular P R x) : ∀ C, C ∈ glueImage I A F x → C ⊆ P := by
  intro C hC
  obtain ⟨i, hi, rfl⟩ := (mem_glueImage_iff I A F x C).mp hC
  exact subset_trans (glue_piece_value_subset hA hB hFiso hi hx)
    (booleanConditions_regular (hB.2.2.1 i hi)).1

theorem glueImage_subset_target (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : IsForcingRegular P R x) : ∀ C, C ∈ glueImage I A F x → C ⊆ b := by
  intro C hC
  obtain ⟨i, hi, rfl⟩ := (mem_glueImage_iff I A F x C).mp hC
  exact subset_trans (glue_piece_value_subset hA hB hFiso hi hx) (hB.2.2.2.1 i hi)

theorem glueValue_regular (hR : IsForcingPreorder P R) (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : IsForcingRegular P R x) : IsForcingRegular P R (glueValue P R I A F x) :=
  regularJoin_regular hR (glueImage_subset_poset hA hB hFiso hx)

/-- A nonzero regular subset of `a` meets one of the pieces. -/
theorem glue_exists_nonempty_piece (hR : IsForcingPreorder P R)
    (hA : IsConePartition P R a I A) (hx : IsForcingRegular P R x) (hxa : x ⊆ a)
    (hxne : x ≠ (∅ : V)) : ∃ i, i ∈ I ∧ x ∩ A ‘ i ≠ (∅ : V) := by
  by_contra hc
  have hc' : ∀ i, i ∈ I → x ∩ A ‘ i = (∅ : V) := by
    intro i hi
    by_contra hne
    exact hc ⟨i, hi, hne⟩
  have hz : regularJoin P R (repl (fun i ↦ x ∩ A ‘ i) (by definability) I) = (∅ : V) :=
    glue_regularJoin_eq_empty hR (fun C hC ↦ by
      obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hC
      exact hc' i hi)
  rw [hA.regularJoin_pieces hR hx hxa] at hz
  exact hxne hz

/-- The glued value of a condition of the cone of `a` is a condition of the cone of `b`. -/
theorem glueValue_mem_cone (hR : IsForcingPreorder P R) (ha : a ∈ booleanConditions P R)
    (hb : b ∈ booleanConditions P R) (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : x ∈ boolCone P R a) : glueValue P R I A F x ∈ boolCone P R b := by
  obtain ⟨hxB, hxa⟩ := (mem_boolCone_sub_iff ha).mp hx
  have hxreg := booleanConditions_regular hxB
  obtain ⟨p, hp⟩ := ((mem_booleanConditions_iff _ _ _).mp hxB).2
  obtain ⟨i, hi, hne⟩ := glue_exists_nonempty_piece hR hA hxreg hxa
    (fun he ↦ not_mem_empty (he ▸ hp))
  have hmem : (F ‘ i) ‘ (x ∩ A ‘ i) ∈ boolCone P R (B ‘ i) :=
    glue_piece_value_mem hA hFiso hi hxreg hne
  have hmemB := (mem_boolCone_sub_iff (hB.2.2.1 i hi)).mp hmem
  obtain ⟨q, hq⟩ := ((mem_booleanConditions_iff _ _ _).mp hmemB.1).2
  refine (mem_boolCone_sub_iff hb).mpr ⟨(mem_booleanConditions_iff _ _ _).mpr
    ⟨glueValue_regular hR hA hB hFiso hxreg, ⟨q, ?_⟩⟩,
      regularJoin_subset hR (glueImage_subset_target hA hB hFiso hxreg)
        (booleanConditions_regular hb)⟩
  exact subset_regularJoin hR ((mem_glueImage_iff I A F x _).mpr ⟨i, hi, rfl⟩)
    (booleanConditions_regular hmemB.1) q hq

/-- The piece of the glued value at `B ‘ j` is the image of the piece of `x` at `A ‘ j`. -/
theorem glueValue_inter_piece (hR : IsForcingPreorder P R) (ha : a ∈ booleanConditions P R)
    (hA : IsConePartition P R a I A) (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : x ∈ boolCone P R a) {j : V} (hj : j ∈ I) :
    glueValue P R I A F x ∩ B ‘ j = (F ‘ j) ‘ (x ∩ A ‘ j) := by
  obtain ⟨hxB, hxa⟩ := (mem_boolCone_sub_iff ha).mp hx
  have hxreg := booleanConditions_regular hxB
  have hBjreg := booleanConditions_regular (hB.2.2.1 j hj)
  have hstep : glueValue P R I A F x ∩ B ‘ j
      = regularJoin P R (repl (fun C ↦ B ‘ j ∩ C) (by definability) (glueImage I A F x)) := by
    show regularJoin P R (glueImage I A F x) ∩ B ‘ j = _
    rw [glue_inter_comm]
    exact inter_regularJoin hR hBjreg (glueImage_subset_poset hA hB hFiso hxreg)
  rw [hstep]
  have hother : ∀ C, C ∈ repl (fun C ↦ B ‘ j ∩ C) (by definability) (glueImage I A F x) →
      ∀ z, z ∈ C → z ∈ (F ‘ j) ‘ (x ∩ A ‘ j) := by
    intro C hC z hz
    obtain ⟨W, hW, rfl⟩ := (repl_spec _).mp hC
    obtain ⟨i, hi, rfl⟩ := (mem_glueImage_iff I A F x W).mp hW
    by_cases hij : i = j
    · subst hij
      exact (mem_inter_iff.mp hz).2
    · exfalso
      obtain ⟨hzj, hzi⟩ := mem_inter_iff.mp hz
      have hzB : z ∈ B ‘ i := glue_piece_value_subset hA hB hFiso hi hxreg z hzi
      have hdisj := hB.2.2.2.2.1 j hj i hi (fun he ↦ hij he.symm)
      rw [SetTheory.mem_ext_iff] at hdisj
      exact not_mem_empty ((hdisj z).mp (mem_inter_iff.mpr ⟨hzj, hzB⟩))
  by_cases hne : x ∩ A ‘ j = (∅ : V)
  · rw [hne, glue_value_empty (hFiso j hj).1]
    refine glue_regularJoin_eq_empty hR (fun C hC ↦ glue_eq_empty_of_forall (fun z hz ↦ ?_))
    have hzz := hother C hC z hz
    rw [hne, glue_value_empty (hFiso j hj).1] at hzz
    exact not_mem_empty hzz
  · have hval := glue_piece_value_mem hA hFiso hj hxreg hne
    have hvalB := (mem_boolCone_sub_iff (hB.2.2.1 j hj)).mp hval
    refine glue_regularJoin_eq_of_mem hR (fun C hC z hz ↦ hother C hC z hz) ?_
      (booleanConditions_regular hvalB.1)
    exact (repl_spec _).mpr ⟨(F ‘ j) ‘ (x ∩ A ‘ j),
      (mem_glueImage_iff I A F x _).mpr ⟨j, hj, rfl⟩,
      ((glue_inter_comm (B ‘ j) ((F ‘ j) ‘ (x ∩ A ‘ j))).trans
        (glue_inter_eq_left hvalB.2)).symm⟩

end Glue


/-! ### Isomorphisms of cones, pointwise -/

section Iso

variable {P R c e f u v : V}

/-- An isomorphism of cones preserves and reflects inclusion. -/
theorem glue_iso_subset_iff (hc : c ∈ booleanConditions P R) (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f)
    (hu : u ∈ boolCone P R c) (hv : v ∈ boolCone P R c) : u ⊆ v ↔ f ‘ u ⊆ f ‘ v := by
  have h := hf.2.2.2 u hu v hv
  rw [kpair_mem_boolConeOrder_iff hc, kpair_mem_boolConeOrder_iff he] at h
  have hfu := (mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hu)
  have hfv := (mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hv)
  have hu' := (mem_boolCone_sub_iff hc).mp hu
  have hv' := (mem_boolCone_sub_iff hc).mp hv
  exact ⟨fun hs ↦ (h.mp ⟨hu', hv', hs⟩).2.2, fun hs ↦ (h.mpr ⟨hfu, hfv, hs⟩).2.2⟩

/-- An isomorphism of cones takes the top to the top. -/
theorem glue_iso_top (hc : c ∈ booleanConditions P R) (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f) : f ‘ c = e := by
  have hcc : c ∈ boolCone P R c := (mem_boolCone_sub_iff hc).mpr ⟨hc, subset_refl c⟩
  have hec : e ∈ boolCone P R e := (mem_boolCone_sub_iff he).mpr ⟨he, subset_refl e⟩
  obtain ⟨w, hw, hfw⟩ := glue_exists_preimage hf hec
  refine SetTheory.subset_antisymm
    ((mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hcc)).2 ?_
  have hstep := (glue_iso_subset_iff hc he hf hw hcc).mp ((mem_boolCone_sub_iff hc).mp hw).2
  rw [hfw] at hstep
  exact hstep

/-- An isomorphism of cones takes disjoint conditions to disjoint conditions. -/
theorem glue_iso_inter_eq_empty (hc : c ∈ booleanConditions P R)
    (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f)
    (hu : u ∈ boolCone P R c) (hv : v ∈ boolCone P R c) (huv : u ∩ v = (∅ : V)) :
    (f ‘ u) ∩ (f ‘ v) = (∅ : V) := by
  by_contra hne
  obtain ⟨z, hz⟩ := glue_exists_mem_of_ne_empty hne
  have hfu := (mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hu)
  have hfv := (mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hv)
  have hWreg : IsForcingRegular P R ((f ‘ u) ∩ (f ‘ v)) :=
    forcingRegular_inter (booleanConditions_regular hfu.1) (booleanConditions_regular hfv.1)
  have hWmem : (f ‘ u) ∩ (f ‘ v) ∈ boolCone P R e :=
    (mem_boolCone_sub_iff he).mpr ⟨(mem_booleanConditions_iff _ _ _).mpr ⟨hWreg, ⟨z, hz⟩⟩,
      subset_trans (fun w hw ↦ (mem_inter_iff.mp hw).1) hfu.2⟩
  obtain ⟨t, ht, hft⟩ := glue_exists_preimage hf hWmem
  have h1 : t ⊆ u := (glue_iso_subset_iff hc he hf ht hu).mpr
    (by rw [hft]; exact fun w hw ↦ (mem_inter_iff.mp hw).1)
  have h2 : t ⊆ v := (glue_iso_subset_iff hc he hf ht hv).mpr
    (by rw [hft]; exact fun w hw ↦ (mem_inter_iff.mp hw).2)
  obtain ⟨s, hs⟩ :=
    ((mem_booleanConditions_iff _ _ _).mp ((mem_boolCone_sub_iff hc).mp ht).1).2
  have hsuv : s ∈ u ∩ v := mem_inter_iff.mpr ⟨h1 s hs, h2 s hs⟩
  rw [huv] at hsuv
  exact not_mem_empty hsuv

/-- A piece map that commutes with meeting `d` also kills `d` on the conditions disjoint from
`d`. The clause `hDpiece` is what makes this true when `d` misses the whole source cone: there
the commutation hypothesis says nothing. -/
theorem glue_iso_inter_d_eq_empty {dd : V} (hc : c ∈ booleanConditions P R)
    (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f)
    (hd : IsForcingRegular P R dd)
    (hequi : ∀ w, w ∈ boolCone P R c → w ∩ dd ≠ (∅ : V) → f ‘ (w ∩ dd) = (f ‘ w) ∩ dd)
    (hDpiece : c ∩ dd = (∅ : V) → e ∩ dd = (∅ : V))
    (hu : u ∈ boolCone P R c) (hud : u ∩ dd = (∅ : V)) : (f ‘ u) ∩ dd = (∅ : V) := by
  have hfu := (mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hu)
  by_cases hcd : c ∩ dd = (∅ : V)
  · refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
    obtain ⟨hzf, hzd⟩ := mem_inter_iff.mp hz
    have hze : z ∈ e ∩ dd := mem_inter_iff.mpr ⟨hfu.2 z hzf, hzd⟩
    rw [hDpiece hcd] at hze
    exact not_mem_empty hze
  · have hcc : c ∈ boolCone P R c := (mem_boolCone_sub_iff hc).mpr ⟨hc, subset_refl c⟩
    have hdc : c ∩ dd ∈ boolCone P R c := (mem_boolCone_sub_iff hc).mpr
      ⟨(mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingRegular_inter (booleanConditions_regular hc) hd,
          glue_exists_mem_of_ne_empty hcd⟩, fun w hw ↦ (mem_inter_iff.mp hw).1⟩
    have hkey : f ‘ (c ∩ dd) = e ∩ dd := by
      rw [hequi c hcc hcd, glue_iso_top hc he hf]
    have hdisj : (f ‘ u) ∩ (f ‘ (c ∩ dd)) = (∅ : V) :=
      glue_iso_inter_eq_empty hc he hf hu hdc (glue_eq_empty_of_forall (fun w hw ↦ by
        obtain ⟨hwu, hwcd⟩ := mem_inter_iff.mp hw
        have hwud : w ∈ u ∩ dd := mem_inter_iff.mpr ⟨hwu, (mem_inter_iff.mp hwcd).2⟩
        rw [hud] at hwud
        exact not_mem_empty hwud))
    rw [hkey] at hdisj
    refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
    obtain ⟨hzf, hzd⟩ := mem_inter_iff.mp hz
    have hzz : z ∈ (f ‘ u) ∩ (e ∩ dd) :=
      mem_inter_iff.mpr ⟨hzf, mem_inter_iff.mpr ⟨hfu.2 z hzf, hzd⟩⟩
    rw [hdisj] at hzz
    exact not_mem_empty hzz

end Iso

/-! ### The glue map is an order isomorphism -/

section Glue2

variable {P R a b I A B F G d x y : V}

theorem glueValue_mono (hR : IsForcingPreorder P R) (ha : a ∈ booleanConditions P R)
    (hA : IsConePartition P R a I A) (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hx : x ∈ boolCone P R a) (hy : y ∈ boolCone P R a) (hxy : x ⊆ y) :
    glueValue P R I A F x ⊆ glueValue P R I A F y := by
  obtain ⟨hxB, hxa⟩ := (mem_boolCone_sub_iff ha).mp hx
  obtain ⟨hyB, hya⟩ := (mem_boolCone_sub_iff ha).mp hy
  have hxreg := booleanConditions_regular hxB
  have hyreg := booleanConditions_regular hyB
  refine regularJoin_subset hR ?_ (glueValue_regular hR hA hB hFiso hyreg)
  intro C hC
  obtain ⟨i, hi, rfl⟩ := (mem_glueImage_iff I A F x C).mp hC
  by_cases hne : x ∩ A ‘ i = (∅ : V)
  · rw [hne, glue_value_empty (hFiso i hi).1]
    exact empty_subset _
  · have hsub : x ∩ A ‘ i ⊆ y ∩ A ‘ i := fun z hz ↦
      mem_inter_iff.mpr ⟨hxy z (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩
    have hyne : y ∩ A ‘ i ≠ (∅ : V) := by
      intro he
      refine hne (glue_eq_empty_of_forall (fun z hz ↦ ?_))
      have hzz := hsub z hz
      rw [he] at hzz
      exact not_mem_empty hzz
    have hmono := (glue_iso_subset_iff (hA.2.2.1 i hi) (hB.2.2.1 i hi) (hFiso i hi)
      (glue_piece_mem_cone hA hi hxreg hne) (glue_piece_mem_cone hA hi hyreg hyne)).mp hsub
    refine subset_trans hmono (subset_regularJoin hR
      ((mem_glueImage_iff I A F y _).mpr ⟨i, hi, rfl⟩) ?_)
    exact booleanConditions_regular ((mem_boolCone_sub_iff (hB.2.2.1 i hi)).mp
      (glue_piece_value_mem hA hFiso hi hyreg hyne)).1

theorem glueValue_inverse (hR : IsForcingPreorder P R) (ha : a ∈ booleanConditions P R)
    (hA : IsConePartition P R a I A) (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hGval : ∀ i, i ∈ I → ∀ w, w ∈ boolCone P R (A ‘ i) → (G ‘ i) ‘ ((F ‘ i) ‘ w) = w)
    (hGzero : ∀ i, i ∈ I → (G ‘ i) ‘ (∅ : V) = (∅ : V))
    (hx : x ∈ boolCone P R a) :
    glueValue P R I B G (glueValue P R I A F x) = x := by
  obtain ⟨hxB, hxa⟩ := (mem_boolCone_sub_iff ha).mp hx
  have hxreg := booleanConditions_regular hxB
  have hval : ∀ i, i ∈ I → (G ‘ i) ‘ (glueValue P R I A F x ∩ B ‘ i) = x ∩ A ‘ i := by
    intro i hi
    rw [glueValue_inter_piece hR ha hA hB hFiso hx hi]
    by_cases hne : x ∩ A ‘ i = (∅ : V)
    · rw [hne, glue_value_empty (hFiso i hi).1, hGzero i hi]
    · exact hGval i hi _ (glue_piece_mem_cone hA hi hxreg hne)
  have himg : glueImage I B G (glueValue P R I A F x)
      = repl (fun i ↦ x ∩ A ‘ i) (by definability) I := by
    apply mem_ext
    intro w
    simp only [mem_glueImage_iff, repl_spec]
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨i, hi, by rw [he]; exact hval i hi⟩
    · rintro ⟨i, hi, he⟩
      exact ⟨i, hi, by rw [he]; exact (hval i hi).symm⟩
  show regularJoin P R (glueImage I B G (glueValue P R I A F x)) = x
  rw [himg]
  exact hA.regularJoin_pieces hR hxreg hxa

theorem glueValue_inter_regular (hR : IsForcingPreorder P R) (ha : a ∈ booleanConditions P R)
    (hb : b ∈ booleanConditions P R) (hA : IsConePartition P R a I A)
    (hB : IsConePartition P R b I B)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i))
    (hd : IsForcingRegular P R d)
    (hDpiece : ∀ i, i ∈ I → (A ‘ i) ∩ d = (∅ : V) → (B ‘ i) ∩ d = (∅ : V))
    (hequi : ∀ i, i ∈ I → ∀ w, w ∈ boolCone P R (A ‘ i) → w ∩ d ≠ (∅ : V) →
      (F ‘ i) ‘ (w ∩ d) = ((F ‘ i) ‘ w) ∩ d)
    (hx : x ∈ boolCone P R a) (hxd : x ∩ d ≠ (∅ : V)) :
    glueValue P R I A F (x ∩ d) = glueValue P R I A F x ∩ d := by
  obtain ⟨hxB, hxa⟩ := (mem_boolCone_sub_iff ha).mp hx
  have hxreg := booleanConditions_regular hxB
  have hxdmem : x ∩ d ∈ boolCone P R a := (mem_boolCone_sub_iff ha).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hxreg hd, glue_exists_mem_of_ne_empty hxd⟩,
      subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) hxa⟩
  have hLB := (mem_boolCone_sub_iff hb).mp (glueValue_mem_cone hR ha hb hA hB hFiso hxdmem)
  have hRB := (mem_boolCone_sub_iff hb).mp (glueValue_mem_cone hR ha hb hA hB hFiso hx)
  refine hB.eq_of_pieces_eq hR (booleanConditions_regular hLB.1) hLB.2
    (forcingRegular_inter (booleanConditions_regular hRB.1) hd)
    (subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) hRB.2) ?_
  intro j hj
  have h1 : glueValue P R I A F (x ∩ d) ∩ B ‘ j = (F ‘ j) ‘ ((x ∩ A ‘ j) ∩ d) := by
    rw [glueValue_inter_piece hR ha hA hB hFiso hxdmem hj, glue_inter_right_comm x d (A ‘ j)]
  have h2 : (glueValue P R I A F x ∩ d) ∩ B ‘ j = ((F ‘ j) ‘ (x ∩ A ‘ j)) ∩ d := by
    rw [glue_inter_right_comm (glueValue P R I A F x) d (B ‘ j),
      glueValue_inter_piece hR ha hA hB hFiso hx hj]
  rw [h1, h2]
  by_cases hne : (x ∩ A ‘ j) ∩ d = (∅ : V)
  · rw [hne, glue_value_empty (hFiso j hj).1]
    by_cases hu : x ∩ A ‘ j = (∅ : V)
    · rw [hu, glue_value_empty (hFiso j hj).1]
      exact (glue_eq_empty_of_forall (fun z hz ↦ not_mem_empty (mem_inter_iff.mp hz).1)).symm
    · exact (glue_iso_inter_d_eq_empty (hA.2.2.1 j hj) (hB.2.2.1 j hj) (hFiso j hj) hd
        (hequi j hj) (hDpiece j hj) (glue_piece_mem_cone hA hj hxreg hu) hne).symm
  · have hu : x ∩ A ‘ j ≠ (∅ : V) := by
      intro he
      refine hne ?_
      rw [he]
      exact glue_eq_empty_of_forall (fun z hz ↦ not_mem_empty (mem_inter_iff.mp hz).1)
    exact hequi j hj _ (glue_piece_mem_cone hA hj hxreg hu) hne

end Glue2

/-! ### The gluing theorems -/

/-- The glued isomorphism, with equivariance for a set `D` of regular sets.

Besides the piecewise equivariance `hequi` this carries the clause `hDpiece`: a `d` missing a
piece `A ‘ i` must miss the matching piece `B ‘ i`. Without it the statement is false. Take a
two-piece partition, `d = A ‘ 1`, and `B ‘ 1` a proper nonzero part of `A ‘ 1`. Then `hequi` is
vacuous at `i = 0` and holds at `i = 1`, while the glued map sends `a ∩ d = d` to `B ‘ 1`, not to
`(glued a) ∩ d = d`. -/
theorem exists_coneIsomorphism_of_conePartitions_equivariant {P R a b I A B F D : V}
    (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (hA : IsConePartition P R a I A) (hB : IsConePartition P R b I B)
    (hF : IsFunction F) (hFdom : domain F = I)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))) (F ‘ i))
    (hD : ∀ d, d ∈ D → IsForcingRegular P R d)
    (hDpiece : ∀ i, i ∈ I → ∀ d, d ∈ D → (A ‘ i) ∩ d = (∅ : V) → (B ‘ i) ∩ d = (∅ : V))
    (hequi : ∀ i, i ∈ I → ∀ d, d ∈ D → ∀ x, x ∈ forcingCone (booleanConditions P R)
        (booleanOrder P R) (A ‘ i) → x ∩ d ≠ (∅ : V) →
        (F ‘ i) ‘ (x ∩ d) = ((F ‘ i) ‘ x) ∩ d) :
    ∃ G, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b)) G ∧
      ∀ d, d ∈ D → ∀ x, x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a →
        x ∩ d ≠ (∅ : V) → G ‘ (x ∩ d) = (G ‘ x) ∩ d := by
  have hFiso' : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (A ‘ i))
      (boolConeOrder P R (A ‘ i)) (boolCone P R (B ‘ i)) (boolConeOrder P R (B ‘ i)) (F ‘ i) :=
    hFiso
  have hGiso : ∀ i, i ∈ I → IsForcingIsomorphism (boolCone P R (B ‘ i))
      (boolConeOrder P R (B ‘ i)) (boolCone P R (A ‘ i)) (boolConeOrder P R (A ‘ i))
      ((conePartitionInverse I F) ‘ i) := by
    intro i hi
    rw [conePartitionInverse_value hi]
    exact isForcingIsomorphism_inverse (hFiso' i hi)
  have hGval : ∀ i, i ∈ I → ∀ w, w ∈ boolCone P R (A ‘ i) →
      ((conePartitionInverse I F) ‘ i) ‘ ((F ‘ i) ‘ w) = w := by
    intro i hi w hw
    rw [conePartitionInverse_value hi]
    exact converseGraph_value_value (hFiso' i hi).1 (hFiso' i hi).2.1 hw
  have hFval : ∀ i, i ∈ I → ∀ w, w ∈ boolCone P R (B ‘ i) →
      (F ‘ i) ‘ (((conePartitionInverse I F) ‘ i) ‘ w) = w := by
    intro i hi w hw
    rw [conePartitionInverse_value hi]
    exact value_converseGraph_value (hFiso' i hi).1 (hFiso' i hi).2.1
      ((hFiso' i hi).2.2.1.symm ▸ hw)
  have hGzero : ∀ i, i ∈ I → ((conePartitionInverse I F) ‘ i) ‘ (∅ : V) = (∅ : V) :=
    fun i hi ↦ glue_value_empty (hGiso i hi).1
  have hFzero : ∀ i, i ∈ I → (F ‘ i) ‘ (∅ : V) = (∅ : V) :=
    fun i hi ↦ glue_value_empty (hFiso' i hi).1
  have hmemA : ∀ z : V, z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a →
      glueValue P R I A F z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b :=
    fun z hz ↦ glueValue_mem_cone hR ha hb hA hB hFiso' hz
  have hmemB : ∀ z : V, z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b →
      glueValue P R I B (conePartitionInverse I F) z ∈
        forcingCone (booleanConditions P R) (booleanOrder P R) a :=
    fun z hz ↦ glueValue_mem_cone hR hb ha hB hA hGiso hz
  have hinvA : ∀ z : V, z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a →
      glueValue P R I B (conePartitionInverse I F) (glueValue P R I A F z) = z :=
    fun z hz ↦ glueValue_inverse hR ha hA hB hFiso' hGval hGzero hz
  have hinvB : ∀ z : V, z ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b →
      glueValue P R I A F (glueValue P R I B (conePartitionInverse I F) z) = z :=
    fun z hz ↦ glueValue_inverse hR hb hB hA hGiso hFval hFzero hz
  refine ⟨definableGraph (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (glueValue P R I A F) (glueValue_definable P R I A F),
    isForcingIsomorphism_of_inverse (glueValue P R I A F)
      (glueValue P R I B (conePartitionInverse I F)) (glueValue_definable P R I A F)
      hmemA hmemB hinvA hinvB ?_, ?_⟩
  · intro u hu v hv
    rw [kpair_mem_coneOrder_iff ha, kpair_mem_coneOrder_iff hb]
    have hu' := (mem_boolCone_sub_iff ha).mp hu
    have hv' := (mem_boolCone_sub_iff ha).mp hv
    have hgu := (mem_boolCone_sub_iff hb).mp (hmemA u hu)
    have hgv := (mem_boolCone_sub_iff hb).mp (hmemA v hv)
    constructor
    · rintro ⟨-, -, huv⟩
      exact ⟨hgu, hgv, glueValue_mono hR ha hA hB hFiso' hu hv huv⟩
    · rintro ⟨-, -, huv⟩
      refine ⟨hu', hv', ?_⟩
      have hstep := glueValue_mono hR hb hB hA hGiso (hmemA u hu) (hmemA v hv) huv
      rw [hinvA u hu, hinvA v hv] at hstep
      exact hstep
  · intro d hdD u hu hud
    have hu' := (mem_boolCone_sub_iff ha).mp hu
    have hudmem : u ∩ d ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a :=
      (mem_boolCone_sub_iff ha).mpr
        ⟨(mem_booleanConditions_iff _ _ _).mpr
          ⟨forcingRegular_inter (booleanConditions_regular hu'.1) (hD d hdD),
            glue_exists_mem_of_ne_empty hud⟩,
          subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) hu'.2⟩
    rw [value_definableGraph _ _ _ hudmem, value_definableGraph _ _ _ hu]
    exact glueValue_inter_regular hR ha hb hA hB hFiso' (hD d hdD)
      (fun i hi ↦ hDpiece i hi d hdD) (fun i hi ↦ hequi i hi d hdD) hu hud

/-- An isomorphism of the cone of `a` onto the cone of `b`, glued from isomorphisms of the pieces
of two cone partitions over a common index set. -/
theorem exists_coneIsomorphism_of_conePartitions {P R a b I A B F : V}
    (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (hA : IsConePartition P R a I A) (hB : IsConePartition P R b I B)
    (hF : IsFunction F) (hFdom : domain F = I)
    (hFiso : ∀ i, i ∈ I → IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))) (F ‘ i)) :
    ∃ G, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b)) G := by
  obtain ⟨G, hG, -⟩ := exists_coneIsomorphism_of_conePartitions_equivariant (D := (∅ : V))
    hR ha hb hA hB hF hFdom hFiso (fun d hd ↦ absurd hd not_mem_empty)
    (fun _ _ d hd ↦ absurd hd not_mem_empty) (fun _ _ d hd ↦ absurd hd not_mem_empty)
  exact ⟨G, hG⟩

end ZFVP
