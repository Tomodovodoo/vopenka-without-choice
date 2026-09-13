import PalomarPreservationBridge.Vocabulary
import PalomarBridge.CodingOperations
import ZFVP.ModelTheory.SymmetricModel

namespace PalomarPreservationBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
@[simp] theorem subset_iff (A B : M) : Subset mem A B ↔ A ⊆ B := Iff.rfl
@[simp] theorem intersection_eq (A B : M) : intersection mem A B = A ∩ B := by
  apply setValue_eq
  simp
@[simp] theorem identity_eq (A : M) : identity mem A = SetTheory.identity A := by
  apply setValue_eq
  simp [mem_identity_iff]
@[simp] theorem inverse_eq (f : M) : inverse mem f = ZFVP.converseGraph f := by
  apply setValue_eq
  intro p
  simp only [ZFVP.converseGraph, mem_sep_iff, mem_prod_iff, coding_pair]
  constructor
  · rintro ⟨⟨x, hx, y, hy, rfl⟩, h⟩
    exact ⟨y, x, by simpa using h, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    exact ⟨⟨y, mem_range_of_kpair_mem h, x, mem_domain_of_kpair_mem h, rfl⟩, by simpa using h⟩
@[simp] theorem injectiveGraph_iff (f : M) : InjectiveGraph mem f ↔ Injective f := by
  simp [InjectiveGraph, Injective]
@[simp] theorem stronger_iff (R q p : M) : Stronger mem R q p ↔ ⟨q, p⟩ₖ ∈ R := by
  simp [Stronger]
@[simp] theorem preorder_iff (P R : M) : Preorder mem P R ↔ ZFVP.IsForcingPreorder P R := by
  simp [Preorder, ZFVP.IsForcingPreorder, subset_def, mem_prod_iff]
@[simp] theorem poset_iff (P R : M) : Poset mem P R ↔ ZFVP.IsForcingPoset P R := by
  simp [Poset, ZFVP.IsForcingPoset]
@[simp] theorem top_iff (P R one : M) : Top mem P R one ↔ ZFVP.IsForcingTop P R one := by
  simp [Top, ZFVP.IsForcingTop]
@[simp] theorem automorphism_iff (P R f : M) :
    Automorphism mem P R f ↔ ZFVP.IsForcingAutomorphism P R f := by
  simp [Automorphism, ZFVP.IsForcingAutomorphism]
@[simp] theorem automorphismGroup_iff (P R group : M) :
    AutomorphismGroup mem P R group ↔ ZFVP.IsForcingAutomorphismGroup P R group := by
  simp [AutomorphismGroup, ZFVP.IsForcingAutomorphismGroup]
@[simp] theorem subgroup_iff (P group H : M) : Subgroup mem P group H ↔ ZFVP.IsForcingSubgroup P group H := by
  simp [Subgroup, ZFVP.IsForcingSubgroup]
@[simp] theorem conjugate_eq (f H : M) : conjugate mem f H = ZFVP.conjugateSubgroup f H := by
  apply setValue_eq
  simp [ZFVP.conjugateSubgroup, repl_spec]
@[simp] theorem normalFilter_iff (P group filter : M) :
    NormalFilter mem P group filter ↔ ZFVP.IsNormalSubgroupFilter P group filter := by
  simp [NormalFilter, ZFVP.IsNormalSubgroupFilter]
@[simp] theorem generic_iff (P R : M) (G : Set M) :
    Generic mem P R G ↔ ZFVP.IsExternalForcingGeneric P R G := by
  simp [Generic, ZFVP.IsExternalForcingGeneric, ZFVP.IsExternalForcingFilter, ZFVP.ForcingDense]

@[simp] theorem subnameClosed_iff (C : M) : SubnameClosed mem C ↔ ZFVP.IsSubnameClosed C := by
  simp [SubnameClosed, ZFVP.IsSubnameClosed]
@[simp] theorem nameClosure_eq (t : M) : nameClosure mem t = ZFVP.nameClosure t := by
  apply setValue_eq
  intro s
  simp only [subnameClosed_iff]
  constructor
  · exact fun hs C hc ht => ZFVP.nameClosure_minimal hc ht s hs
  · exact fun h => h _ (ZFVP.nameClosure_closed t) (ZFVP.mem_nameClosure_self t)
@[simp] theorem name_iff (P t : M) : Name mem P t ↔ ZFVP.IsForcingName P t := by
  simp [Name, ZFVP.IsForcingName]
@[simp] theorem recursion_iff (C : M) (step : M → M → M) (f : M) :
    Recursion mem C step f ↔ ZFVP.IsSubnameRecursion C step f := by
  simp [Recursion, ZFVP.IsSubnameRecursion]

theorem recursion_eq (step : M → M → M) (hstep : ℒₛₑₜ-function₂ step) (t : M) :
    recursion mem step t = ZFVP.subnameRecursion step hstep t := by
  have he : ∃ f : M, Recursion mem (nameClosure mem t) step f := by
    simpa using ZFVP.subnameRecursion_exists (ZFVP.nameClosure_closed t) step hstep
  have hs := Classical.epsilon_spec he
  have hf : Classical.epsilon (Recursion mem (nameClosure mem t) step) =
      ZFVP.subnameRecursionTable step hstep t := by
    apply (ZFVP.subnameRecursionTable_eq_iff step hstep t _).mpr
    simpa using hs
  unfold recursion ZFVP.subnameRecursion
  rw [hf, coding_value]

@[simp] theorem actionStep_eq (f t g : M) : actionStep mem f t g = ZFVP.nameActionStep f t g := by
  apply setValue_eq
  simp [ZFVP.nameActionStep, repl_spec]
@[simp] theorem action_eq (f t : M) : action mem f t = ZFVP.nameAction f t := by
  unfold action
  have he : actionStep mem f = ZFVP.nameActionStep f := by funext a b; exact actionStep_eq _ _ _
  rw [he]
  exact recursion_eq _ (by definability) t
@[simp] theorem stabilizer_eq (group t : M) : stabilizer mem group t = ZFVP.nameStabilizer group t := by
  apply setValue_eq
  simp [ZFVP.nameStabilizer]
@[simp] theorem hereditarilySymmetric_iff (P group filter t : M) :
    HereditarilySymmetric mem P group filter t ↔ ZFVP.IsHereditarilySymmetricName P group filter t := by
  simp [HereditarilySymmetric, ZFVP.IsHereditarilySymmetricName]

@[simp] theorem equalityTest_iff (P R : M) (E : M → M → M) (s t p : M) :
    EqualityTest mem P R E s t p ↔ ZFVP.AtomicEqualityTest P R E s t p := by
  simp [EqualityTest, ZFVP.AtomicEqualityTest]
@[simp] theorem equalityConditions_eq (P R s t f : M) :
    equalityConditions mem P R s t f = ZFVP.atomicEqualityConditions P R s t f := by
  apply setValue_eq
  simp [ZFVP.atomicEqualityConditions, ZFVP.AtomicEqualityTest, EqualityTest]
@[simp] theorem equalityRowStep_eq (P R C s f : M) :
    equalityRowStep mem P R C s f = ZFVP.atomicEqualityRowStep P R C s f := by
  apply setValue_eq
  simp [ZFVP.atomicEqualityRowStep, ZFVP.mem_definableGraph_iff]
@[simp] theorem equality_eq (P R s t : M) : equality mem P R s t = ZFVP.atomicEquality P R s t := by
  unfold equality
  simp only [nameClosure_eq]
  have he : equalityRowStep mem P R (ZFVP.nameClosure t) =
      ZFVP.atomicEqualityRowStep P R (ZFVP.nameClosure t) := by
    funext a b; exact equalityRowStep_eq _ _ _ _ _
  rw [he]
  rw [recursion_eq _ (by definability), coding_value]
  rfl
@[simp] theorem membership_eq (P R s t : M) : membership mem P R s t = ZFVP.atomicMembership P R s t := by
  apply setValue_eq
  simp [ZFVP.atomicMembership, ZFVP.AtomicMembershipTest]

/-- The independently specified data give the exact existing symmetric context. -/
def toContext (d : SymmetricData mem) : ZFVP.SymmetricContext M where
  P := d.P
  R := d.R
  one := d.one
  G := d.G
  Γ := d.group
  F := d.filter
  order := ((poset_iff _ _).mp d.poset).1
  top := (top_iff _ _ _).mp d.top
  generic := (generic_iff _ _ _).mp d.generic
  poset := (poset_iff _ _).mp d.poset
  group := (automorphismGroup_iff _ _ _).mp d.automorphisms
  normal := (normalFilter_iff _ _ _).mp d.normal

end PalomarPreservationBridge



