import ZFVP.ModelTheory.SchmerlCodedFiniteDomains
import ZFVP.ModelTheory.SchmerlInfinitaryFunctionClauses

/-! The full represented poset of internal finite binary functions, with its
domain projection. These are actual ambient sets, uniformly in the parameter. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedFunctionNodes (M s : V) : V :=
  codedParameterSet M (encodeMembershipFormula finiteBinaryFunctionFormula) s

noncomputable def codedFunctionOrder (M s : V) : V :=
  codedBinaryOn M (encodeMembershipFormula (“p q. p ⊆ q” : SetTheorySemisentence 2))
    (codedFunctionNodes M s) (codedFunctionNodes M s)

noncomputable def codedFunctionDomains (M s : V) : V :=
  codedBinaryOn M (encodeMembershipFormula (f“p a. a = !domain.dfn p” : SetTheorySemisentence 2))
    (codedFunctionNodes M s) (codedFiniteDomains M s)

def functionOrderFormula : SetTheorySemisentence 3 :=
  f“p q s. !finiteBinaryFunctionFormula p s ∧ !finiteBinaryFunctionFormula q s ∧ p ⊆ q”

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp
attribute [local irreducible] codedParameterSet codedBinaryOn

instance codedFunctionNodes_definable : ℒₛₑₜ-function₂[V] codedFunctionNodes := by unfold codedFunctionNodes; definability
instance codedFunctionOrder_definable : ℒₛₑₜ-function₂[V] codedFunctionOrder := by unfold codedFunctionOrder; definability
instance codedFunctionDomains_definable : ℒₛₑₜ-function₂[V] codedFunctionDomains := by unfold codedFunctionDomains; definability

theorem codedFunctionNodes_isCodedDefinable {M s : V} (hs : s ∈ structureDomain M) :
    IsCodedDefinableSet M (codedFunctionNodes M s) :=
  codedParameterSet_isCodedDefinable M finiteBinaryFunctionFormula hs

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem functionNode_mem_iff (s p : W) :
    (R.equiv p).val ∈ codedFunctionNodes R.code (R.equiv s).val ↔
      p ∈ finitePartialFunctions s ((2 : ℕ) : W) := by
  rw [codedFunctionNodes, R.mem_parameterSet_iff, eval_finiteBinaryFunctionFormula]

theorem mem_functionNodes_iff (s : W) (x : V) :
    x ∈ codedFunctionNodes R.code (R.equiv s).val ↔
      ∃ p : W, (R.equiv p).val = x ∧ p ∈ finitePartialFunctions s ((2 : ℕ) : W) := by
  constructor
  · intro hx
    have hxD : x ∈ R.carrier := by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp hx).1
    let p : W := R.equiv.symm ⟨x, hxD⟩
    have hp : (R.equiv p).val = x := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    exact ⟨p, hp, (R.functionNode_mem_iff s p).mp (hp.symm ▸ hx)⟩
  · rintro ⟨p, rfl, hp⟩
    exact (R.functionNode_mem_iff s p).mpr hp

theorem functionOrder_iff (s p q : W) :
    ⟨(R.equiv p).val, (R.equiv q).val⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val ↔
      p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧
        q ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧ p ⊆ q := by
  rw [codedFunctionOrder, pair_mem_codedBinaryOn, R.functionNode_mem_iff,
    R.functionNode_mem_iff, R.codedBinary_iff]
  simp

theorem functionOrder_isCodedDefinable (s : W) :
    IsCodedDefinableRelation R.code (codedFunctionOrder R.code (R.equiv s).val) := by
  apply R.parameter_relation_definable_of_formula functionOrderFormula s
  · intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (codedBinaryOn_subset _ _ _ _ p hp)
    exact kpair_mem_iff.mpr ⟨by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp ha).1, by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp hb).1⟩
  · intro p q
    rw [R.functionOrder_iff]
    simpa only [functionOrderFormula, eval_finiteBinaryFunctionFormula] using
      (show (p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧
        q ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧ p ⊆ q) ↔
        functionOrderFormula.Evalb ![p, q, s] from by
        simp [functionOrderFormula, finiteBinaryFunctionFormula, mem_finitePartialFunctions]
        rfl)

theorem functionOrder_poset (s : W) :
    IsForcingPoset (codedFunctionNodes R.code (R.equiv s).val)
      (codedFunctionOrder R.code (R.equiv s).val) := by
  refine ⟨⟨codedBinaryOn_subset _ _ _ _, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
    exact (R.functionOrder_iff s p p).mpr ⟨hp, hp, subset_refl _⟩
  · intro x hx y hy z hz hxy hyz
    obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
    obtain ⟨q, rfl, _⟩ := (R.mem_functionNodes_iff s y).mp hy
    obtain ⟨r, rfl, hr⟩ := (R.mem_functionNodes_iff s z).mp hz
    exact (R.functionOrder_iff s p r).mpr ⟨hp, hr,
      subset_trans ((R.functionOrder_iff s p q).mp hxy).2.2 ((R.functionOrder_iff s q r).mp hyz).2.2⟩
  · intro x hx y hy hxy hyx
    obtain ⟨p, rfl, _⟩ := (R.mem_functionNodes_iff s x).mp hx
    obtain ⟨q, rfl, _⟩ := (R.mem_functionNodes_iff s y).mp hy
    exact congrArg (fun p ↦ (R.equiv p).val) (SetTheory.subset_antisymm
      ((R.functionOrder_iff s p q).mp hxy).2.2 ((R.functionOrder_iff s q p).mp hyx).2.2)

theorem functionDomains_iff (s p a : W) :
    ⟨(R.equiv p).val, (R.equiv a).val⟩ₖ ∈ codedFunctionDomains R.code (R.equiv s).val ↔
      p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧ a = domain p := by
  have heval : (f“p a. a = !domain.dfn p” : SetTheorySemisentence 2).Evalb ![p, a] ↔ a = domain p := by simp
  rw [codedFunctionDomains, pair_mem_codedBinaryOn, R.functionNode_mem_iff,
    R.finiteDomain_mem_iff, R.codedBinary_iff, heval]
  constructor
  · rintro ⟨hp, _, he⟩
    exact ⟨hp, he⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨hp, ⟨((mem_finitePartialFunctions _ _ _).mp hp).2.2, finitePartialFunction_domain hp⟩, rfl⟩

theorem functionDomains_function (s : W) :
    codedFunctionDomains R.code (R.equiv s).val ∈
      codedFiniteDomains R.code (R.equiv s).val ^ codedFunctionNodes R.code (R.equiv s).val := by
  apply mem_function_iff.mpr
  refine ⟨codedBinaryOn_subset _ _ _ _, ?_⟩
  intro x hx
  obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
  refine ⟨(R.equiv (domain p)).val, (R.functionDomains_iff s p _).mpr ⟨hp, rfl⟩, ?_⟩
  intro y hy
  have hyD := ((pair_mem_codedBinaryOn _ _ _ _ _ _).mp hy).2.1
  obtain ⟨a, rfl, _⟩ := (R.mem_finiteDomains_iff s y).mp hyD
  exact congrArg (fun a ↦ (R.equiv a).val) ((R.functionDomains_iff s p a).mp hy).2

theorem functionDomains_value (s p : W) (hp : p ∈ finitePartialFunctions s ((2 : ℕ) : W)) :
    (codedFunctionDomains R.code (R.equiv s).val) ‘ (R.equiv p).val = (R.equiv (domain p)).val := by
  let : IsFunction (codedFunctionDomains R.code (R.equiv s).val) := IsFunction.of_mem (R.functionDomains_function s)
  exact value_eq_of_kpair_mem ((R.functionDomains_iff s p _).mpr ⟨hp, rfl⟩)

theorem functionDomains_monotone (s : W) {x y : V}
    (hx : x ∈ codedFunctionNodes R.code (R.equiv s).val) (hy : y ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hxy : ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val) :
    ⟨(codedFunctionDomains R.code (R.equiv s).val) ‘ x,
      (codedFunctionDomains R.code (R.equiv s).val) ‘ y⟩ₖ ∈ codedFiniteDomainOrder R.code (R.equiv s).val := by
  obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
  obtain ⟨q, rfl, hq⟩ := (R.mem_functionNodes_iff s y).mp hy
  rw [R.functionDomains_value s p hp, R.functionDomains_value s q hq, R.finiteDomainOrder_iff]
  refine ⟨⟨((mem_finitePartialFunctions _ _ _).mp hp).2.2, finitePartialFunction_domain hp⟩,
    ⟨((mem_finitePartialFunctions _ _ _).mp hq).2.2, finitePartialFunction_domain hq⟩, ?_⟩
  intro a ha
  obtain ⟨b, hab⟩ := mem_domain_iff.mp ha
  exact mem_domain_of_kpair_mem (((R.functionOrder_iff s p q).mp hxy).2.2 _ hab)

theorem functionOrder_of_common_above_of_domains (s : W) {x y z : V}
    (hx : x ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hy : y ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hz : z ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hxz : ⟨x, z⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val)
    (hyz : ⟨y, z⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val)
    (hdom : ⟨(codedFunctionDomains R.code (R.equiv s).val) ‘ x,
      (codedFunctionDomains R.code (R.equiv s).val) ‘ y⟩ₖ ∈ codedFiniteDomainOrder R.code (R.equiv s).val) :
    ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val := by
  obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
  obtain ⟨q, rfl, hq⟩ := (R.mem_functionNodes_iff s y).mp hy
  obtain ⟨r, rfl, hr⟩ := (R.mem_functionNodes_iff s z).mp hz
  let : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  let : IsFunction q := ((mem_finitePartialFunctions _ _ _).mp hq).2.1
  let : IsFunction r := ((mem_finitePartialFunctions _ _ _).mp hr).2.1
  rw [R.functionDomains_value s p hp, R.functionDomains_value s q hq, R.finiteDomainOrder_iff] at hdom
  apply (R.functionOrder_iff s p q).mpr
  refine ⟨hp, hq, FunctionTreeNode.subset_of_compatible hdom.2.2 ?_⟩
  intro a b d hab had
  exact IsFunction.unique (((R.functionOrder_iff s p r).mp hxz).2.2 _ hab)
    (((R.functionOrder_iff s q r).mp hyz).2.2 _ had)

theorem functionDomains_comparable_injective (s : W) {x y : V}
    (hx : x ∈ codedFunctionNodes R.code (R.equiv s).val) (hy : y ∈ codedFunctionNodes R.code (R.equiv s).val)
    (hxy : ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val)
    (he : (codedFunctionDomains R.code (R.equiv s).val) ‘ x =
      (codedFunctionDomains R.code (R.equiv s).val) ‘ y) : x = y := by
  apply (R.functionOrder_poset s).2 x hx y hy hxy
  apply R.functionOrder_of_common_above_of_domains s hy hx hy ((R.functionOrder_poset s).1.2.1 y hy) hxy
  rw [he]
  exact (R.finiteDomainOrder_poset s).1.2.1 _ (function_value_mem (R.functionDomains_function s) hy)

theorem functionDomains_onto (s : W) {a : V}
    (ha : a ∈ codedFiniteDomains R.code (R.equiv s).val) :
    ∃ x ∈ codedFunctionNodes R.code (R.equiv s).val,
      (codedFunctionDomains R.code (R.equiv s).val) ‘ x = a := by
  obtain ⟨d, rfl, hd⟩ := (R.mem_finiteDomains_iff s a).mp ha
  let p : W := constantGraph d ((0 : ℕ) : W)
  have hf : p ∈ ((2 : ℕ) : W) ^ d := constantGraph_mem_function _ _ _ (by simp)
  have hp : p ∈ finitePartialFunctions s ((2 : ℕ) : W) :=
    (mem_finitePartialFunctions _ _ _).mpr ⟨subset_trans (subset_prod_of_mem_function hf)
      (prod_subset_prod_of_subset hd.2 (subset_refl _)), IsFunction.of_mem hf,
      (domain_eq_of_mem_function hf).symm ▸ hd.1⟩
  refine ⟨(R.equiv p).val, (R.functionNode_mem_iff s p).mpr hp, ?_⟩
  rw [R.functionDomains_value s p hp, domain_eq_of_mem_function hf]

theorem functionDomains_predecessor (s : W) {x a : V}
    (hx : x ∈ codedFunctionNodes R.code (R.equiv s).val)
    (ha : a ∈ codedFiniteDomains R.code (R.equiv s).val)
    (hax : ⟨a, (codedFunctionDomains R.code (R.equiv s).val) ‘ x⟩ₖ ∈
      codedFiniteDomainOrder R.code (R.equiv s).val) :
    ∃ y ∈ codedFunctionNodes R.code (R.equiv s).val,
      ⟨y, x⟩ₖ ∈ codedFunctionOrder R.code (R.equiv s).val ∧
        (codedFunctionDomains R.code (R.equiv s).val) ‘ y = a := by
  obtain ⟨p, rfl, hp⟩ := (R.mem_functionNodes_iff s x).mp hx
  obtain ⟨d, rfl, _⟩ := (R.mem_finiteDomains_iff s a).mp ha
  rw [R.functionDomains_value s p hp, R.finiteDomainOrder_iff] at hax
  have hq := finitePartialFunction_subset hp (restrict_subset p d)
  refine ⟨(R.equiv (p ↾ d)).val, (R.functionNode_mem_iff s _).mpr hq,
    (R.functionOrder_iff s _ p).mpr ⟨hq, hp, restrict_subset _ _⟩, ?_⟩
  rw [R.functionDomains_value s _ hq, domain_restrict_eq, inter_eq_right_of_subset hax.2.2]

end ZFVP.BinaryRelationRepresentation
