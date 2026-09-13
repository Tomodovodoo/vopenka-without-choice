import ZFVP.ModelTheory.SolovayPointwiseDefinable
import ZFVP.ModelTheory.CompleteSubalgebra
import ZFVP.SetTheory.SubnameRecursion

/-! Values of names that lie in the extension by a complete subalgebra.

This is the route to the forward half of Karagila-Schilhan Lemma 9.3 that does not go through the
Galois closure statement refuted in `ZFVP/ModelTheory/LevySupportAlgebraClosure.lean`.

Three things are proved.

The first is a dictionary between the complete subalgebras of `RO(P)` and those of `RO(RO(P))`.
The regular cone of a regular set of `P`, taken inside the Boolean completion `B = RO(P) \ {0}`,
is the set of Boolean conditions below it (`mem_coneRegular_boolean_iff`), and this map takes
negations to negations and joins to joins, so the preimage of a complete subalgebra of `RO(B)`
under it is a complete subalgebra of `RO(P)` (`isCompleteSubalgebra_algebraPreimage`). Combined
with `coneRegular_regularJoin` this identifies the support algebra of a set of nice names, which
lives in `RO(B)`, with a complete subalgebra `supportAlgebraBase` of `RO(P)`, and every element of
that algebra is fixed by every automorphism in the forced stabilizer of the names
(`supportAlgebraBase_fixed_of_forcedStabilizer`). The converse of that last statement is the
Galois closure refuted in `ZFVP/ModelTheory/LevySupportAlgebraClosure.lean`.

The second is the evaluation lemma, which is what the earlier attempts were missing. For a name
`τ` over `B` write `booleanValueBase ν μ` for the element of `RO(P)` whose cone is the Boolean
value `‖ν ∈ μ‖`. If every such value for a pair `ν ∈ dom μ` with `μ` in the name closure of `τ`
lies in a complete subalgebra `D`, then the value of `τ` lies in the intermediate extension
`V[G ∩ D]` (`inSubalgebraModel_of_hereditarilyIn`). The proof replaces `τ` by its reduct
`nameReduct`, defined by recursion on names, whose conditions are the values `booleanValueBase ν μ`
themselves, so that it is a name over the sub-poset of `D`; the reduct is forced equal to `τ` by
every condition (`forcedEqual_nameReduct`), which is proved by induction on names and so stays
inside the ground model, where induction on names is available. This replaces the valuation
recursion inside the extension that `ZFVP/ModelTheory/SolovayPointwiseDefinable.lean` asks for and
that is not available.

The third is the unconditional case. A nice name over `K` has all the Boolean values of its name
closure in the support algebra of any set of names containing it: at the top level they are the
support values themselves, and inside the check names they are the top of the completion. So the
value of a nice name, in particular of each of the names generating the Solovay symmetric system,
lies in the extension by the support algebra (`ForcingContext.inSubalgebraModel_of_niceName`).

For a general hereditarily symmetric name what is left is the hypothesis
`ClosureValuesInSupportAlgebra`: the Boolean values of the membership statements inside the name
closure lie in the support algebra of a support of the name. Given it,
`inSubalgebraModel_of_hereditarilySymmetric` is the forward half of Lemma 9.3.
`closureValuesInSupportAlgebra_of_galois` shows that the hypothesis holds for a name all of whose
subnames have the one support, as soon as the Galois step `GaloisStep` of
`ZFVP/ModelTheory/SolovayPointwiseDefinable.lean` does, so nothing beyond that step is hidden in
it. `GaloisStep` is neither proved nor refuted here or anywhere in the library; what is refuted is
the stronger statement about arbitrary conditions determined below an ordinal. For names whose
subnames have different supports the hypothesis also needs the supports to be amalgamated into one
algebra, which the finiteness of a single support does not give. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Cones of regular sets inside the Boolean completion -/

/-- The regular cone of a regular set `A ⊆ P`, taken in the Boolean completion, is the set of
Boolean conditions contained in `A`. Unlike `mem_coneRegular_booleanOrder_iff` this does not ask
`A` to be nonzero. -/
theorem mem_coneRegular_boolean_iff {P R A C : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) :
    C ∈ coneRegular (booleanConditions P R) (booleanOrder P R) A ↔
      C ∈ booleanConditions P R ∧ C ⊆ A := by
  constructor
  · intro h
    obtain ⟨hC, hh⟩ := mem_coneRegular_iff.mp h
    refine ⟨hC, fun p hp ↦ ?_⟩
    by_contra hpA
    have hpP : p ∈ P := booleanConditions_subset hC p hp
    obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hpP hpA hA.2.2
    have hqP : q ∈ P := forcingNegation_subset _ _ _ q hq
    have hqC : q ∈ C := (booleanConditions_regular hC).2.1 p hp q hqP hqp
    have hDB : coneRegular P R q ∈ booleanConditions P R :=
      coneRegular_mem_booleanConditions hR hqP
    have hDC : ⟨coneRegular P R q, C⟩ₖ ∈ booleanOrder P R :=
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hDB, hC, coneRegular_subset_of_mem hR (booleanConditions_regular hC) hqC⟩
    obtain ⟨E, hE, hEA, hED⟩ := hh _ hDB hDC
    obtain ⟨-, -, hEsubA⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hEA
    obtain ⟨-, -, hEsubD⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hED
    obtain ⟨r, hr⟩ := booleanConditions_nonempty hE
    have hrA : r ∈ A := hEsubA r hr
    have hrP : r ∈ P := hA.1 r hrA
    obtain ⟨-, hcone⟩ := mem_coneRegular_iff.mp (hEsubD r hr)
    obtain ⟨s, hsP, hsq, hsr⟩ := hcone r hrP (hR.2.1 r hrP)
    exact ((mem_forcingNegation_iff _ _ _ _).mp hq).2 s hsP hsq (hA.2.1 r hrA s hsP hsr)
  · rintro ⟨hC, hCA⟩
    obtain ⟨p, hp⟩ := booleanConditions_nonempty hC
    have hAB : A ∈ booleanConditions P R := (mem_booleanConditions_iff _ _ _).mpr ⟨hA, p, hCA p hp⟩
    refine mem_coneRegular_iff.mpr ⟨hC, fun D hD hDC ↦ ⟨D, hD, ?_, ?_⟩⟩
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hD, hAB,
        fun z hz ↦ hCA z (((kpair_mem_booleanOrder_iff _ _ _ _).mp hDC).2.2 z hz)⟩
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hD, hD, subset_refl _⟩

/-- Cones take negations to negations. -/
theorem coneRegular_forcingNegation {P R A : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) :
    coneRegular (booleanConditions P R) (booleanOrder P R) (forcingNegation P R A) =
      forcingNegation (booleanConditions P R) (booleanOrder P R)
        (coneRegular (booleanConditions P R) (booleanOrder P R) A) := by
  apply mem_ext
  intro C
  rw [mem_coneRegular_boolean_iff hR (forcingNegation_regular hR hA.2.1), mem_forcingNegation_iff]
  constructor
  · rintro ⟨hC, hCn⟩
    refine ⟨hC, fun D hD hDC hDcone ↦ ?_⟩
    obtain ⟨-, hDA⟩ := (mem_coneRegular_boolean_iff hR hA).mp hDcone
    obtain ⟨-, -, hDsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hDC
    obtain ⟨r, hr⟩ := booleanConditions_nonempty hD
    have hrn : r ∈ forcingNegation P R A := hCn r (hDsub r hr)
    exact ((mem_forcingNegation_iff _ _ _ _).mp hrn).2 r (hA.1 r (hDA r hr))
      (hR.2.1 r (hA.1 r (hDA r hr))) (hDA r hr)
  · rintro ⟨hC, hCn⟩
    refine ⟨hC, ?_⟩
    have hCreg := booleanConditions_regular hC
    rw [subset_forcingNegation_iff hR hCreg hA.1]
    by_contra hne
    obtain ⟨p, hp⟩ : ∃ p, p ∈ C ∩ A := by
      by_contra h
      push Not at h
      exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd hz (h z), fun hz ↦ absurd hz not_mem_empty⟩))
    obtain ⟨hpC, hpA⟩ := mem_inter_iff.mp hp
    have hpP : p ∈ P := hA.1 p hpA
    have hDB : coneRegular P R p ∈ booleanConditions P R :=
      coneRegular_mem_booleanConditions hR hpP
    refine hCn _ hDB ((kpair_mem_booleanOrder_iff _ _ _ _).mpr
      ⟨hDB, hC, coneRegular_subset_of_mem hR hCreg hpC⟩) ?_
    exact (mem_coneRegular_boolean_iff hR hA).mpr ⟨hDB, coneRegular_subset_of_mem hR hA hpA⟩

/-- Cones take joins to joins: the cone of a regular join is the join of the cones. -/
theorem coneRegular_regularJoin_eq {P R X Y : V} (hR : IsForcingPreorder P R)
    (hX : ∀ b ∈ X, IsForcingRegular P R b)
    (hY : ∀ C, C ∈ Y ↔ ∃ b ∈ X, C = coneRegular (booleanConditions P R) (booleanOrder P R) b) :
    coneRegular (booleanConditions P R) (booleanOrder P R) (regularJoin P R X) =
      regularJoin (booleanConditions P R) (booleanOrder P R) Y := by
  have hjoin : IsForcingRegular P R (regularJoin P R X) :=
    regularJoin_regular hR (fun b hb ↦ (hX b hb).1)
  apply mem_ext
  intro C
  rw [mem_coneRegular_boolean_iff hR hjoin, mem_regularJoin_iff]
  constructor
  · rintro ⟨hC, hCj⟩
    refine ⟨hC, fun D hD hDC ↦ ?_⟩
    obtain ⟨-, -, hDsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hDC
    obtain ⟨p, hp⟩ := booleanConditions_nonempty hD
    have hpP : p ∈ P := booleanConditions_subset hD p hp
    have hpj : p ∈ regularJoin P R X := hCj p (hDsub p hp)
    obtain ⟨-, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hpj
    obtain ⟨r, ⟨b, hb, hrb⟩, hrp⟩ := hh p hpP (hR.2.1 p hpP)
    have hrP : r ∈ P := (hX b hb).1 r hrb
    have hrD : r ∈ D := (booleanConditions_regular hD).2.1 p hp r hrP hrp
    have hEB : coneRegular P R r ∈ booleanConditions P R :=
      coneRegular_mem_booleanConditions hR hrP
    refine ⟨coneRegular P R r, ⟨coneRegular (booleanConditions P R) (booleanOrder P R) b,
      (hY _).mpr ⟨b, hb, rfl⟩, ?_⟩, ?_⟩
    · exact (mem_coneRegular_boolean_iff hR (hX b hb)).mpr
        ⟨hEB, coneRegular_subset_of_mem hR (hX b hb) hrb⟩
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hEB, hD, coneRegular_subset_of_mem hR (booleanConditions_regular hD) hrD⟩
  · rintro ⟨hC, hh⟩
    refine ⟨hC, fun p hp ↦ ?_⟩
    have hCreg := booleanConditions_regular hC
    have hpP : p ∈ P := hCreg.1 p hp
    refine (mem_regularJoin_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
    have hqC : q ∈ C := hCreg.2.1 p hp q hq hqp
    have hDB : coneRegular P R q ∈ booleanConditions P R :=
      coneRegular_mem_booleanConditions hR hq
    obtain ⟨E, ⟨C₀, hC₀, hEC₀⟩, hED⟩ := hh _ hDB ((kpair_mem_booleanOrder_iff _ _ _ _).mpr
      ⟨hDB, hC, coneRegular_subset_of_mem hR hCreg hqC⟩)
    obtain ⟨b, hb, rfl⟩ := (hY C₀).mp hC₀
    obtain ⟨hEB, hEb⟩ := (mem_coneRegular_boolean_iff hR (hX b hb)).mp hEC₀
    obtain ⟨-, -, hEsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hED
    obtain ⟨r, hr⟩ := booleanConditions_nonempty hEB
    have hrb : r ∈ b := hEb r hr
    have hrP : r ∈ P := (hX b hb).1 r hrb
    obtain ⟨-, hcone⟩ := mem_coneRegular_iff.mp (hEsub r hr)
    obtain ⟨s, hsP, hsq, hsr⟩ := hcone r hrP (hR.2.1 r hrP)
    exact ⟨s, ⟨b, hb, (hX b hb).2.1 r hrb s hsP hsr⟩, hsq⟩

/-! ### Complete subalgebras of `RO(P)` from complete subalgebras of `RO(RO(P))` -/

/-- The regular sets of `P` whose cone in the Boolean completion lies in `S`. -/
noncomputable def algebraPreimage (P R S : V) : V :=
  {b ∈ regularSets P R ; coneRegular (booleanConditions P R) (booleanOrder P R) b ∈ S}

theorem mem_algebraPreimage_iff (P R S b : V) :
    b ∈ algebraPreimage P R S ↔ IsForcingRegular P R b ∧
      coneRegular (booleanConditions P R) (booleanOrder P R) b ∈ S := by
  unfold algebraPreimage
  rw [mem_sep_iff, mem_regularSets_iff]

/-- The preimage of a complete subalgebra of `RO(B)` under the cone map is a complete subalgebra
of `RO(P)`. -/
theorem isCompleteSubalgebra_algebraPreimage {P R S : V} (hR : IsForcingPreorder P R)
    (hP : ∃ p, p ∈ P)
    (hS : IsCompleteSubalgebra (booleanConditions P R) (booleanOrder P R) S) :
    IsCompleteSubalgebra P R (algebraPreimage P R S) := by
  refine ⟨fun b hb ↦ (mem_sep_iff.mp hb).1, ?_, ?_, ?_⟩
  · refine (mem_algebraPreimage_iff _ _ _ _).mpr ⟨forcingRegular_top P R, ?_⟩
    have htop : coneRegular (booleanConditions P R) (booleanOrder P R) P =
        booleanConditions P R := by
      apply mem_ext
      intro C
      rw [mem_coneRegular_boolean_iff hR (forcingRegular_top P R)]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, booleanConditions_subset h⟩⟩
    rw [htop]
    exact hS.2.1
  · intro b hb
    obtain ⟨hbreg, hbS⟩ := (mem_algebraPreimage_iff _ _ _ _).mp hb
    refine (mem_algebraPreimage_iff _ _ _ _).mpr ⟨forcingNegation_regular hR hbreg.2.1, ?_⟩
    rw [coneRegular_forcingNegation hR hbreg]
    exact hS.2.2.1 _ hbS
  · intro X hX
    have hXreg : ∀ b ∈ X, IsForcingRegular P R b := fun b hb ↦
      ((mem_algebraPreimage_iff _ _ _ _).mp (hX b hb)).1
    refine (mem_algebraPreimage_iff _ _ _ _).mpr
      ⟨regularJoin_regular hR (fun b hb ↦ (hXreg b hb).1), ?_⟩
    have hYdef : ∀ C, C ∈ sep S (fun C ↦ ∃ b ∈ X,
        C = coneRegular (booleanConditions P R) (booleanOrder P R) b) (by definability) ↔
        ∃ b ∈ X, C = coneRegular (booleanConditions P R) (booleanOrder P R) b := by
      intro C
      rw [mem_sep_iff]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      obtain ⟨b, hb, rfl⟩ := h
      exact ((mem_algebraPreimage_iff _ _ _ _).mp (hX b hb)).2
    rw [coneRegular_regularJoin_eq hR hXreg hYdef]
    exact hS.2.2.2 _ (fun C hC ↦ (mem_sep_iff.mp hC).1)

/-! ### Boolean values as conditions of the completion -/

/-- The Boolean value `‖ν ∈ μ‖` read as an element of `RO(P)`: the join of the set of conditions
of the completion forcing `ν ∈ μ`. -/
noncomputable def booleanValueBase (P R ν μ : V) : V :=
  regularJoin P R (atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ)

instance booleanValueBase_definable (P R : V) : ℒₛₑₜ-function₂[V] (booleanValueBase P R) := by
  have := regularJoin_definable_one P R
  have := atomicMembership_definable (booleanConditions P R) (booleanOrder P R)
  unfold booleanValueBase
  definability

theorem booleanValueBase_regular {P R : V} (hR : IsForcingPreorder P R) (ν μ : V) :
    IsForcingRegular P R (booleanValueBase P R ν μ) :=
  regularJoin_regular hR (fun A hA ↦ booleanConditions_subset
    (atomicMembership_subset _ _ _ _ A hA))

/-- The cone of the Boolean value is the set of conditions forcing the membership, provided the
value is nonzero. -/
theorem coneRegular_booleanValueBase {P R ν μ : V} (hR : IsForcingPreorder P R)
    (hne : ∃ p, p ∈ booleanValueBase P R ν μ) :
    coneRegular (booleanConditions P R) (booleanOrder P R) (booleanValueBase P R ν μ) =
      atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ := by
  have hreg : IsForcingRegular (booleanConditions P R) (booleanOrder P R)
      (atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ) :=
    atomicMembership_regular (booleanOrder_poset P R).1 ν μ
  have hnonempty : ∃ C, C ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ := by
    by_contra h
    push Not at h
    have : atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd hz (h z), fun hz ↦ absurd hz not_mem_empty⟩)
    obtain ⟨p, hp⟩ := hne
    rw [booleanValueBase, this, regularJoin_empty hR] at hp
    exact not_mem_empty hp
  exact coneRegular_regularJoin hR ((mem_booleanConditions_iff _ _ _).mpr ⟨hreg, hnonempty⟩)

/-- A condition of the completion below a nonzero Boolean value forces the membership. -/
theorem mem_atomicMembership_of_subset_booleanValueBase {P R ν μ C : V}
    (hR : IsForcingPreorder P R) (hC : C ∈ booleanConditions P R)
    (hsub : C ⊆ booleanValueBase P R ν μ) :
    C ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ := by
  obtain ⟨p, hp⟩ := booleanConditions_nonempty hC
  rw [← coneRegular_booleanValueBase hR ⟨p, hsub p hp⟩]
  exact (mem_coneRegular_boolean_iff hR (booleanValueBase_regular hR ν μ)).mpr ⟨hC, hsub⟩

/-- A condition of the completion forcing the membership is below the Boolean value. -/
theorem subset_booleanValueBase {P R ν μ C : V} (hR : IsForcingPreorder P R)
    (hC : C ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ) :
    C ⊆ booleanValueBase P R ν μ :=
  subset_regularJoin_of_mem hR (atomicMembership_subset _ _ _ _) hC

/-! ### The reduct of a name over the Boolean completion -/

/-- The step of the recursion producing the reduct: replace the conditions of `μ` by the Boolean
values of the membership statements, and the subnames by their reducts. -/
noncomputable def nameReductStep (P R μ f : V) : V :=
  sep ((range f) ×ˢ regularSets P R)
    (fun z ↦ ∃ ν ∈ domain μ, (∃ p, p ∈ booleanValueBase P R ν μ) ∧
      z = ⟨f ‘ ν, booleanValueBase P R ν μ⟩ₖ) (by definability)

theorem nameReductStep_definable (P R : V) : ℒₛₑₜ-function₂[V] (nameReductStep P R) := by
  have h : ℒₛₑₜ-relation₃ (fun w μ f : V ↦ ∀ z, z ∈ w ↔ z ∈ (range f) ×ˢ regularSets P R ∧
      ∃ ν ∈ domain μ, (∃ p, p ∈ booleanValueBase P R ν μ) ∧
        z = ⟨f ‘ ν, booleanValueBase P R ν μ⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameReductStep P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [nameReductStep, mem_sep_iff]

/-- The reduct of a name: the same value, but with the Boolean value of each membership statement
as the condition attached to the reduct of the subname. -/
noncomputable def nameReduct (P R μ : V) : V :=
  subnameRecursion (nameReductStep P R) (nameReductStep_definable P R) μ

instance nameReduct_definable (P R : V) : ℒₛₑₜ-function₁[V] (nameReduct P R) := by
  unfold nameReduct
  infer_instance

theorem mem_nameReductStep_iff (P R μ f z : V) :
    z ∈ nameReductStep P R μ f ↔ z ∈ (range f) ×ˢ regularSets P R ∧
      ∃ ν ∈ domain μ, (∃ p, p ∈ booleanValueBase P R ν μ) ∧
        z = ⟨f ‘ ν, booleanValueBase P R ν μ⟩ₖ := mem_sep_iff

theorem nameReduct_eq (P R μ : V) :
    nameReduct P R μ = nameReductStep P R μ
      (definableGraph (domain μ) (nameReduct P R) (nameReduct_definable P R)) :=
  subnameRecursion_equation (nameReductStep P R) (nameReductStep_definable P R) μ

theorem mem_nameReduct_iff {P R : V} (hR : IsForcingPreorder P R) (μ z : V) :
    z ∈ nameReduct P R μ ↔ ∃ ν ∈ domain μ, (∃ p, p ∈ booleanValueBase P R ν μ) ∧
      z = ⟨nameReduct P R ν, booleanValueBase P R ν μ⟩ₖ := by
  rw [nameReduct_eq, mem_nameReductStep_iff]
  constructor
  · rintro ⟨-, ν, hν, hne, he⟩
    exact ⟨ν, hν, hne, by rwa [value_definableGraph _ _ _ hν] at he⟩
  · rintro ⟨ν, hν, hne, rfl⟩
    have hval : (definableGraph (domain μ) (nameReduct P R) (nameReduct_definable P R)) ‘ ν =
        nameReduct P R ν := value_definableGraph _ _ _ hν
    refine ⟨?_, ν, hν, hne, by rw [hval]⟩
    refine mem_prod_iff.mpr ⟨nameReduct P R ν, ?_, booleanValueBase P R ν μ, ?_, rfl⟩
    · rw [range_definableGraph, repl_spec]
      exact ⟨ν, hν, rfl⟩
    · exact (mem_regularSets_iff _ _ _).mpr (booleanValueBase_regular hR ν μ)

/-- The reduct of a name is forced equal to it. -/
theorem forcedEqual_nameReduct {P R : V} (hR : IsForcingPreorder P R) (τ : V) :
    ForcedEqual (booleanConditions P R) (booleanOrder P R) (nameReduct P R τ) τ := by
  have hB := (booleanOrder_poset P R).1
  have h := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    (fun μ ↦ ForcedEqual (booleanConditions P R) (booleanOrder P R) (nameReduct P R μ) μ)
    (by definability) ?_
  · exact h τ (mem_nameClosure_self τ)
  intro μ hμ ih p hp
  have ihν : ∀ ν ∈ domain μ, ForcedEqual (booleanConditions P R) (booleanOrder P R)
      (nameReduct P R ν) ν := by
    intro ν hν
    obtain ⟨s, hs⟩ := mem_domain_iff.mp hν
    exact ih ν (nameClosure_closed τ μ hμ ν hν) (rank_subname_lt hs)
  refine (mem_atomicEquality_iff _ _ _ _ _).mpr ⟨hp, ?_, ?_⟩
  · intro υ s hs q hq hqp hqs
    obtain ⟨ν, hν, -, hz⟩ := (mem_nameReduct_iff hR μ _).mp hs
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hz
    obtain ⟨-, -, hqsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hqs
    have hqm : q ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ :=
      mem_atomicMembership_of_subset_booleanValueBase hR hq hqsub
    obtain ⟨-, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hqm
    obtain ⟨r, hr, hrq, ν', t, ht, hrt, he⟩ := hh q hq (hB.2.1 q hq)
    exact ⟨r, hr, hrq, ν', t, ht, hrt,
      atomicEquality_trans hB _ ν ν' r (ihν ν hν r hr) he⟩
  · intro ν t ht q hq hqp hqt
    obtain ⟨-, htB, hqsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hqt
    have hνd : ν ∈ domain μ := mem_domain_iff.mpr ⟨t, ht⟩
    have htm : t ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ :=
      atomicMembership_of_pair hB htB ht
    have hqm : q ∈ atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ :=
      atomicMembership_mono hB htm hq hqt
    have hqb : q ⊆ booleanValueBase P R ν μ := subset_booleanValueBase hR hqm
    obtain ⟨x, hx⟩ := booleanConditions_nonempty hq
    have hne : ∃ x, x ∈ booleanValueBase P R ν μ := ⟨x, hqb x hx⟩
    have hbB : booleanValueBase P R ν μ ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨booleanValueBase_regular hR ν μ, hne⟩
    refine ⟨q, hq, hB.2.1 q hq, nameReduct P R ν, booleanValueBase P R ν μ,
      (mem_nameReduct_iff hR μ _).mpr ⟨ν, hνd, hne, rfl⟩, ?_, ihν ν hνd q hq⟩
    exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hq, hbB, hqb⟩

/-! ### Names whose Boolean values lie in a subalgebra -/

/-- Every Boolean value of a membership statement between a name in the closure of `τ` and one of
its subnames lies in `D`. -/
def IsHereditarilyInAlgebra (P R D τ : V) : Prop :=
  ∀ μ ∈ nameClosure τ, ∀ ν ∈ domain μ, booleanValueBase P R ν μ ∈ D

instance isHereditarilyInAlgebra_definable (P R : V) :
    ℒₛₑₜ-relation[V] (IsHereditarilyInAlgebra P R) := by
  unfold IsHereditarilyInAlgebra
  definability

/-- If all those values lie in `D`, the reduct is a name for the sub-poset of `D`. -/
theorem nameReduct_isForcingName {P R D τ : V} (hR : IsForcingPreorder P R)
    (hτ : IsHereditarilyInAlgebra P R D τ) :
    IsForcingName (subalgebraConditions P R D) (nameReduct P R τ) := by
  have h := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    (fun μ ↦ IsForcingName (subalgebraConditions P R D) (nameReduct P R μ)) (by definability) ?_
  · exact h τ (mem_nameClosure_self τ)
  intro μ hμ ih
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, hν, hne, rfl⟩ := (mem_nameReduct_iff hR μ _).mp hz
  obtain ⟨s, hs⟩ := mem_domain_iff.mp hν
  refine ⟨nameReduct P R ν, booleanValueBase P R ν μ, ?_, rfl,
    ih ν (nameClosure_closed τ μ hμ ν hν) (rank_subname_lt hs)⟩
  exact (mem_subalgebraConditions_iff _ _ _ _).mpr ⟨hτ μ hμ ν hν,
    (mem_booleanConditions_iff _ _ _).mpr ⟨booleanValueBase_regular hR ν μ, hne⟩⟩

namespace ForcingContext

variable (A : ForcingContext V) {D : V} (hD : IsCompleteSubalgebra A.P A.R D)

theorem inSubalgebraModel_ofName_liftName (ρ : ForcingName (A.subalgebraContext hD).P) :
    A.InSubalgebraModel hD (A.booleanContext.ofName (A.booleanContext.liftName
      (A.subalgebraConditions_subset_boolean (D := D)) (A.top_mem_subalgebraConditions hD)
      (hD.trace_generic A.order A.generic) ρ)) :=
  A.booleanContext.inRestrictedModel_ofName _ _ _ ρ

/-- The value of a name all of whose Boolean values lie in a complete subalgebra `D` is in the
intermediate extension `V[G ∩ D]`. -/
theorem inSubalgebraModel_of_hereditarilyIn (τ : ForcingName A.booleanContext.P)
    (hτ : IsHereditarilyInAlgebra A.P A.R D τ.val) :
    A.InSubalgebraModel hD (A.booleanContext.ofName τ) := by
  have hname : IsForcingName (subalgebraConditions A.P A.R D) (nameReduct A.P A.R τ.val) :=
    nameReduct_isForcingName A.order hτ
  have h := A.inSubalgebraModel_ofName_liftName hD ⟨nameReduct A.P A.R τ.val, hname⟩
  obtain ⟨p, hpG⟩ := A.booleanContext.generic.1.2.1
  have heq : A.booleanContext.ofName (A.booleanContext.liftName
      (A.subalgebraConditions_subset_boolean (D := D)) (A.top_mem_subalgebraConditions hD)
      (hD.trace_generic A.order A.generic) ⟨nameReduct A.P A.R τ.val, hname⟩) =
      A.booleanContext.ofName τ :=
    (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mpr
      ⟨p, hpG, forcedEqual_nameReduct A.order τ.val p (A.booleanContext.generic.1.1 p hpG)⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.trans heq⟩

end ForcingContext

/-! ### The support algebra as a complete subalgebra of `RO(P)` -/

/-- The support algebra of `E`, which lives in `RO(RO(P))`, read as a complete subalgebra
of `RO(P)`. -/
noncomputable def supportAlgebraBase (P R one K E : V) : V :=
  algebraPreimage P R (supportAlgebra (booleanConditions P R) (booleanOrder P R) one K E)

theorem isCompleteSubalgebra_supportAlgebraBase {P R : V} (hR : IsForcingPreorder P R)
    (hP : ∃ p, p ∈ P) (one K E : V) :
    IsCompleteSubalgebra P R (supportAlgebraBase P R one K E) :=
  isCompleteSubalgebra_algebraPreimage hR hP
    (generatedSubalgebra_complete (booleanOrder_poset P R).1
      (supportValues_subset_regularSets (booleanOrder_poset P R).1 one K E))

theorem coneRegular_empty_boolean {P R : V} (hR : IsForcingPreorder P R) :
    coneRegular (booleanConditions P R) (booleanOrder P R) (∅ : V) = (∅ : V) := by
  apply mem_ext
  intro C
  rw [mem_coneRegular_boolean_iff hR (forcingRegular_empty hR)]
  constructor
  · rintro ⟨hC, hCe⟩
    obtain ⟨p, hp⟩ := booleanConditions_nonempty hC
    exact absurd (hCe p hp) not_mem_empty
  · intro h
    exact absurd h not_mem_empty

/-- A Boolean value whose set of conditions is in the support algebra is, as an element of
`RO(P)`, in the base support algebra. -/
theorem booleanValueBase_mem_supportAlgebraBase {P R one K E ν μ : V} (hR : IsForcingPreorder P R)
    (h : atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ ∈
      supportAlgebra (booleanConditions P R) (booleanOrder P R) one K E) :
    booleanValueBase P R ν μ ∈ supportAlgebraBase P R one K E := by
  refine (mem_algebraPreimage_iff _ _ _ _).mpr ⟨booleanValueBase_regular hR ν μ, ?_⟩
  by_cases hne : ∃ p, p ∈ booleanValueBase P R ν μ
  · rw [coneRegular_booleanValueBase hR hne]
    exact h
  · have hzero : booleanValueBase P R ν μ = (∅ : V) := by
      push Not at hne
      exact mem_ext (fun z ↦ ⟨fun hz ↦ absurd hz (hne z), fun hz ↦ absurd hz not_mem_empty⟩)
    rw [hzero, coneRegular_empty_boolean hR]
    exact empty_mem_supportAlgebra P R one K E

/-- Every automorphism of the completion in the forced stabilizer of `E` fixes every condition of
the completion that lies in the base support algebra. The converse, that a condition fixed by the
whole forced stabilizer lies in the algebra, is the Galois step refuted in
`ZFVP/ModelTheory/LevySupportAlgebraClosure.lean`. -/
theorem supportAlgebraBase_fixed_of_forcedStabilizer {P R one K E b Θ : V}
    (hR : IsForcingPreorder P R) (hone : IsForcingTop (booleanConditions P R) (booleanOrder P R) one)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions P R) (booleanOrder P R) one K σ)
    (hΘ : Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E)
    (hb : b ∈ booleanConditions P R) (hbD : b ∈ supportAlgebraBase P R one K E) :
    Θ ‘ b = b := by
  have hΘa : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ :=
    (mem_forcingAutomorphisms_iff _ _ _).mp ((mem_forcedStabilizer _ _ _ _ _).mp hΘ).1
  have hcone := ((mem_algebraPreimage_iff _ _ _ _).mp hbD).2
  have hfix := supportAlgebra_fixed_of_forcedStabilizer (booleanOrder_poset P R)
    (forcingAutomorphisms_group _ _) hone hE hΘ _ hcone
  rw [imageAction_coneRegular hΘa hb] at hfix
  exact coneRegular_injective_of_separative (booleanOrder_poset P R)
    (booleanOrder_separative hR) (function_value_mem hΘa.1 hb) hb hfix

/-! ### The forward half of Lemma 9.3, modulo the values of the name closure -/

/-- Every Boolean value of a membership statement inside the name closure of `τ` lies in the
support algebra of `E`. This is what is left of Karagila-Schilhan Lemma 9.3: the support of `τ`
gives the invariance of each such value under the forced stabilizer of `E`, and the missing step
is from that invariance to membership in the algebra. -/
def ClosureValuesInSupportAlgebra (P R one K E τ : V) : Prop :=
  ∀ μ ∈ nameClosure τ, ∀ ν ∈ domain μ,
    atomicMembership (booleanConditions P R) (booleanOrder P R) ν μ ∈
      supportAlgebra (booleanConditions P R) (booleanOrder P R) one K E

/-- Given the Galois step, a name all of whose subnames are fixed by the forced stabilizer of `E`
has all the Boolean values of its name closure in the support algebra of `E`. So the hypothesis
`ClosureValuesInSupportAlgebra` below is exactly the Galois step for names with a single support,
and nothing else. -/
theorem closureValuesInSupportAlgebra_of_galois {P R one K E τ : V} (hR : IsForcingPreorder P R)
    (hgal : GaloisStep P R one K E) (hτ : IsForcingName (booleanConditions P R) τ)
    (hfix : ∀ μ ∈ nameClosure τ, ∀ Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E, nameAction Θ μ = μ) :
    ClosureValuesInSupportAlgebra P R one K E τ := by
  intro μ hμ ν hν
  have hνc : ν ∈ nameClosure τ := nameClosure_closed τ μ hμ ν hν
  exact atomicMembership_mem_supportAlgebra hR hgal (forcingName_mem_closure hτ hνc)
    (forcingName_mem_closure hτ hμ) (fun Θ hΘ ↦ ⟨hfix ν hνc Θ hΘ, hfix μ hμ Θ hΘ⟩)

theorem isHereditarilyInAlgebra_of_closureValues {P R one K E τ : V} (hR : IsForcingPreorder P R)
    (h : ClosureValuesInSupportAlgebra P R one K E τ) :
    IsHereditarilyInAlgebra P R (supportAlgebraBase P R one K E) τ :=
  fun μ hμ ν hν ↦ booleanValueBase_mem_supportAlgebraBase hR (h μ hμ ν hν)

/-! ### The unconditional case: nice names -/

/-- The name closure of a nice name over `K` consists of the name itself and the checks of the
elements of the transitive closure of `K`. -/
theorem nameClosure_niceName_subset {P one K σ : V} (hσ : IsNiceName P one K σ) :
    nameClosure σ ⊆ insert σ (repl (checkName one) (by definability) (transitiveClosure K)) := by
  refine nameClosure_minimal ?_ (mem_insert.mpr (Or.inl rfl))
  intro μ hμ ν hν
  obtain ⟨s, hs⟩ := mem_domain_iff.mp hν
  have hcheck : ∀ y ∈ transitiveClosure K, ∀ z, ⟨ν, z⟩ₖ ∈ checkName one y →
      ν ∈ repl (checkName one) (by definability) (transitiveClosure K) := by
    intro y hy z hz
    obtain ⟨w, hw, hpair⟩ := (mem_checkName_iff one y _).mp hz
    obtain ⟨rfl, -⟩ := kpair_iff.mp hpair
    exact (repl_spec _).mpr ⟨w, (transitiveClosure_transitive K).transitive y hy w hw, rfl⟩
  rcases mem_insert.mp hμ with rfl | hμ'
  · obtain ⟨k, hk, p, -, hz⟩ := hσ _ hs
    obtain ⟨rfl, -⟩ := kpair_iff.mp hz
    exact mem_insert.mpr (Or.inr ((repl_spec _).mpr
      ⟨k, subset_transitiveClosure K k hk, rfl⟩))
  · obtain ⟨y, hy, rfl⟩ := (repl_spec _).mp hμ'
    exact mem_insert.mpr (Or.inr (hcheck y hy s hs))

/-- A nice name over `K` in `E` has all the Boolean values of its name closure in the support
algebra of `E`: the values at the top level are support values of `E`, and the values inside the
checks are the top of the completion. -/
theorem closureValuesInSupportAlgebra_of_niceName {P R K E σ : V}
    (hP : ∃ p, p ∈ P) (hσ : IsNiceName (booleanConditions P R) P K σ) (hσE : σ ∈ E) :
    ClosureValuesInSupportAlgebra P R P K E σ := by
  have hone : IsForcingTop (booleanConditions P R) (booleanOrder P R) P := booleanOrder_top hP
  have hBo : IsForcingPreorder (booleanConditions P R) (booleanOrder P R) :=
    (booleanOrder_poset P R).1
  intro μ hμ ν hν
  obtain ⟨s, hs⟩ := mem_domain_iff.mp hν
  rcases mem_insert.mp (nameClosure_niceName_subset hσ μ hμ) with rfl | hμ'
  · obtain ⟨k, hk, p, -, hz⟩ := hσ _ hs
    obtain ⟨rfl, -⟩ := kpair_iff.mp hz
    exact supportValues_subset_supportAlgebra _ _ _ _ _ _
      (atomicMembership_mem_supportValues hk hσE)
  · obtain ⟨y, -, rfl⟩ := (repl_spec _).mp hμ'
    obtain ⟨w, hw, hpair⟩ := (mem_checkName_iff P y _).mp hs
    obtain ⟨rfl, -⟩ := kpair_iff.mp hpair
    have htop : atomicMembership (booleanConditions P R) (booleanOrder P R)
        (checkName P w) (checkName P y) = booleanConditions P R := by
      apply mem_ext
      intro p
      rw [mem_atomicMembership_checkName_iff hBo hone]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hw⟩⟩
    rw [htop]
    exact top_mem_generatedSubalgebra _ _ _

namespace ForcingContext

/-- Unconditional case of the forward half of Lemma 9.3: the value of a nice name over `K` lies in
the extension by the support algebra of any set `E` of names containing it. -/
theorem inSubalgebraModel_of_niceName (A : ForcingContext V) {K E : V}
    (σ : ForcingName A.booleanContext.P)
    (hσ : IsNiceName (booleanConditions A.P A.R) A.P K σ.val) (hσE : σ.val ∈ E) :
    ∃ hD : IsCompleteSubalgebra A.P A.R (supportAlgebraBase A.P A.R A.P K E),
      A.InSubalgebraModel hD (A.booleanContext.ofName σ) := by
  have hP : ∃ p, p ∈ A.P := ⟨A.one, A.top.1⟩
  have hD := isCompleteSubalgebra_supportAlgebraBase A.order hP A.P K E
  exact ⟨hD, A.inSubalgebraModel_of_hereditarilyIn hD σ
    (isHereditarilyInAlgebra_of_closureValues A.order
      (closureValuesInSupportAlgebra_of_niceName hP hσ hσE))⟩

end ForcingContext


/-- The value of a hereditarily symmetric name of the Solovay system lies in the extension by the
support algebra of a finite set of saturated nice names supporting it, provided the Boolean values
inside its name closure lie in that algebra. -/
theorem inSubalgebraModel_of_hereditarilySymmetric {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : (levySolovayContext κ hG).Name)
    (hobs : ∀ E : V,
      (∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E ⊆
        nameStabilizer (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))) τ.val →
      ClosureValuesInSupportAlgebra (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E τ.val) :
    ∃ E : V, IsInternallyFinite E ∧
      (∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) ∧
      ∃ D : V, ∃ hD : IsCompleteSubalgebra (levyContext κ hG).P (levyContext κ hG).R D,
        (levyContext κ hG).InSubalgebraModel hD
          ((levyContext κ hG).booleanEquiv
            (solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ))) := by
  obtain ⟨E, hEf, hEs, hEst⟩ := (levyContext κ hG).solovay_exists_support τ
  refine ⟨E, hEf, hEs, supportAlgebraBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
    ((ω : V) ×ˢ (ω : V)) E, isCompleteSubalgebra_supportAlgebraBase (levyCollapse_poset κ).1
      ⟨∅, empty_mem_levyCollapse κ⟩ _ _ _, ?_⟩
  have hval := isHereditarilyInAlgebra_of_closureValues (levyCollapse_poset κ).1
    (hobs E hEs hEst)
  obtain ⟨y, hy⟩ := (levyContext κ hG).inSubalgebraModel_of_hereditarilyIn
    (isCompleteSubalgebra_supportAlgebraBase (levyCollapse_poset κ).1
      ⟨∅, empty_mem_levyCollapse κ⟩ (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) E)
    ⟨τ.val, τ.property.1⟩ hval
  refine ⟨y, hy.trans ?_⟩
  show (levyContext κ hG).booleanContext.ofName ⟨τ.val, τ.property.1⟩ =
    (levyContext κ hG).booleanEquiv ((levyContext κ hG).booleanEquiv.symm
      ((levySolovayContext κ hG).toOrdinary ((levySolovayContext κ hG).ofName τ)))
  exact (Equiv.apply_symm_apply _ _).symm

/-- The same for a name with a single support: if every name in the closure of `τ` is fixed by the
forced stabilizer of `E`, then given the Galois step for `E` the value of `τ` lies in the extension
by the support algebra of `E` itself. -/
theorem inSubalgebraModel_of_uniformSupport {κ : V} {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (τ : (levySolovayContext κ hG).Name) (E : V)
    (hgal : GaloisStep (levyCollapse κ) (levyOrder κ) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) E)
    (hfix : ∀ μ ∈ nameClosure τ.val, ∀ Θ ∈ forcedStabilizer
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) E, nameAction Θ μ = μ) :
    ∃ hD : IsCompleteSubalgebra (levyContext κ hG).P (levyContext κ hG).R
      (supportAlgebraBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E),
      (levyContext κ hG).InSubalgebraModel hD
        ((levyContext κ hG).booleanEquiv
          (solovaySymmetricInclusion hG ((levySolovayContext κ hG).ofName τ))) := by
  have hD := isCompleteSubalgebra_supportAlgebraBase (levyCollapse_poset κ).1
    ⟨∅, empty_mem_levyCollapse κ⟩ (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) E
  refine ⟨hD, ?_⟩
  have hval := isHereditarilyInAlgebra_of_closureValues (levyCollapse_poset κ).1
    (closureValuesInSupportAlgebra_of_galois (one := levyCollapse κ)
      (levyCollapse_poset κ).1 hgal τ.property.1 hfix)
  obtain ⟨y, hy⟩ := (levyContext κ hG).inSubalgebraModel_of_hereditarilyIn hD
    ⟨τ.val, τ.property.1⟩ hval
  refine ⟨y, hy.trans ?_⟩
  show (levyContext κ hG).booleanContext.ofName ⟨τ.val, τ.property.1⟩ =
    (levyContext κ hG).booleanEquiv ((levyContext κ hG).booleanEquiv.symm
      ((levySolovayContext κ hG).toOrdinary ((levySolovayContext κ hG).ofName τ)))
  exact (Equiv.apply_symm_apply _ _).symm

end ZFVP
