import ZFVP.ModelTheory.SchmerlCodedFunctionCandidatePreservation
import ZFVP.ModelTheory.SchmerlCodedClassColors

/-! Exact interpretation of finite-function candidates and their cofinality
test, followed by an original membership code for every preserved candidate. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (s : W)
variable {κ c g : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val)
  (codedFiniteDomainOrder R.code (R.equiv s).val) c)
variable (hg : g ∈ R.carrier ^ R.carrier)

include hc

omit [IsOrdinal κ] in
theorem selectedFunctionNode_iff (p : W) :
    (R.equiv p).val ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c ↔
      p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧ (R.equiv (domain p)).val ∈ range c := by
  let : IsFunction c := IsFunction.of_mem hc.1
  rw [mem_codedSelectedFunctionNodes, R.functionNode_mem_iff]
  by_cases hp : p ∈ finitePartialFunctions s ((2 : ℕ) : W)
  · rw [and_iff_right hp, and_iff_right hp, R.functionDomains_value s p hp]
    constructor
    · rintro ⟨i, hi, he⟩
      rw [he]
      exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hc.1] using hi))
    · intro hd
      obtain ⟨i, hi⟩ := mem_range_iff.mp hd
      exact ⟨i, by simpa only [domain_eq_of_mem_function hc.1] using mem_domain_of_kpair_mem hi,
        (value_eq_of_kpair_mem hi).symm⟩
  · simp only [hp, false_and]

omit [IsOrdinal κ] in
theorem functionFilterCandidate_iff {b p : W} (hb : b ∈ finitePartialFunctions s ((2 : ℕ) : W)) :
    functionFilterCandidate s (fun d ↦ (R.equiv d).val ∈ range c)
      (fun x y ↦ R.representedColor hg x = R.representedColor hg y) b p ↔
      (R.equiv p).val ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g (R.equiv b).val := by
  rw [functionFilterCandidate, mem_codedFunctionCandidate]
  constructor
  · rintro ⟨hp, y, hy, hdy, hcone, hpy⟩
    refine ⟨(R.functionNode_mem_iff s p).mpr hp, (R.functionNode_mem_iff s b).mpr hb,
      (R.equiv y).val, (R.selectedFunctionNode_iff s hc y).mpr ⟨hy, hdy⟩, ?_,
      (R.functionOrder_iff s p y).mpr ⟨hp, hy, hpy⟩⟩
    rcases hcone with hyb | ⟨hby, he⟩
    · exact Or.inl ((R.functionOrder_iff s y b).mpr ⟨hy, hb, hyb⟩)
    · exact Or.inr ⟨(R.functionOrder_iff s b y).mpr ⟨hb, hy, hby⟩,
        (R.representedColor_eq_iff hg b y).mp he⟩
  · rintro ⟨hp, _, y, hy, hcone, hpy⟩
    obtain ⟨q, hq, _⟩ := (R.mem_functionNodes_iff s y).mp ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hy).1
    rw [← hq] at hy hcone hpy
    have hq' := (R.selectedFunctionNode_iff s hc q).mp hy
    refine ⟨(R.functionNode_mem_iff s p).mp hp, q, hq'.1, hq'.2, ?_,
      ((R.functionOrder_iff s p q).mp hpy).2.2⟩
    rcases hcone with hqb | ⟨hbq, he⟩
    · exact Or.inl ((R.functionOrder_iff s q b).mp hqb).2.2
    · exact Or.inr ⟨((R.functionOrder_iff s b q).mp hbq).2.2,
        (R.representedColor_eq_iff hg b q).mpr he⟩

omit [IsOrdinal κ] in
theorem functionFilterCandidate_cofinality {b : W} (hb : b ∈ finitePartialFunctions s ((2 : ℕ) : W))
    (hcof : ∀ d : W, (R.equiv d).val ∈ range c → ∃ p : W,
      functionFilterCandidate s (fun a ↦ (R.equiv a).val ∈ range c)
        (fun x y ↦ R.representedColor hg x = R.representedColor hg y) b p ∧ d ⊆ domain p) :
    ∀ i ∈ κ, ∃ x ∈ codedFunctionCandidate R.code (R.equiv s).val κ c g (R.equiv b).val,
      ⟨c ‘ i, (codedFunctionDomains R.code (R.equiv s).val) ‘ x⟩ₖ ∈
        codedFiniteDomainOrder R.code (R.equiv s).val := by
  let : IsFunction c := IsFunction.of_mem hc.1
  intro i hi
  obtain ⟨d, hd, hdfin, hds⟩ := (R.mem_finiteDomains_iff s _).mp (function_value_mem hc.1 hi)
  have hdr : (R.equiv d).val ∈ range c := by
    rw [hd]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hc.1] using hi))
  obtain ⟨p, hp, hdp⟩ := hcof d hdr
  have hpfin := hp.1
  refine ⟨(R.equiv p).val, (R.functionFilterCandidate_iff s hc hg hb).mp hp, ?_⟩
  rw [R.functionDomains_value s p hpfin, ← hd, R.finiteDomainOrder_iff]
  exact ⟨⟨hdfin, hds⟩, ⟨((mem_finitePartialFunctions _ _ _).mp hpfin).2.2,
    finitePartialFunction_domain hpfin⟩, hdp⟩

omit [IsOrdinal κ] in
theorem representedColor_functionWeak
    (hweak : InternallyWeakSpecialization (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) g)
    (x y z : W)
    (hx : x ∈ finitePartialFunctions s ((2 : ℕ) : W)) (hdx : (R.equiv (domain x)).val ∈ range c)
    (hy : y ∈ finitePartialFunctions s ((2 : ℕ) : W)) (hdy : (R.equiv (domain y)).val ∈ range c)
    (hz : z ∈ finitePartialFunctions s ((2 : ℕ) : W)) (hdz : (R.equiv (domain z)).val ∈ range c)
    (hxy : x ⊆ y) (hxz : x ⊆ z)
    (hexy : R.representedColor hg x = R.representedColor hg y)
    (hexz : R.representedColor hg x = R.representedColor hg z) : y ⊆ z ∨ z ⊆ y := by
  have hxT := (R.selectedFunctionNode_iff s hc x).mpr ⟨hx, hdx⟩
  have hyT := (R.selectedFunctionNode_iff s hc y).mpr ⟨hy, hdy⟩
  have hzT := (R.selectedFunctionNode_iff s hc z).mpr ⟨hz, hdz⟩
  have hh := hweak _ hxT _ hyT _ hzT
    ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr
      ⟨(R.functionOrder_iff s x y).mpr ⟨hx, hy, hxy⟩, hxT, hyT⟩)
    ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr
      ⟨(R.functionOrder_iff s x z).mpr ⟨hx, hz, hxz⟩, hxT, hzT⟩)
    ((R.representedColor_eq_iff hg x y).mp hexy) ((R.representedColor_eq_iff hg x z).mp hexz)
  exact hh.imp (fun h ↦ ((R.functionOrder_iff s y z).mp (mem_inter_iff.mp h).1).2.2)
    (fun h ↦ ((R.functionOrder_iff s z y).mp (mem_inter_iff.mp h).1).2.2)

variable {U : Type*} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit hg in
theorem endExtension_functionFilterCandidate_has_code (j : MembershipEndExtension V U)
    (hω : HasStandardOmega V) (hRubin : IsCodedRubin R.code κ)
    (hpres : ∀ B : U,
      IsInternalCofinalBranch (j (codedSelectedFunctionNodes R.code (R.equiv s).val κ c))
        (j (codedSelectedFunctionOrder R.code (R.equiv s).val κ c)) (j κ)
        (j (codedSelectedFunctionRank R.code (R.equiv s).val κ c)) B →
      ∃ A : V, IsInternalCofinalBranch (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
        (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
        (codedSelectedFunctionRank R.code (R.equiv s).val κ c) A ∧ j A = B)
    {g : U} (hg : g ∈ (R.endExtension j).carrier ^ (R.endExtension j).carrier)
    (hweak : InternallyWeakSpecialization
      (codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c))
      (codedSelectedFunctionOrder (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c)) g)
    {b : W} (hb : b ∈ finitePartialFunctions s ((2 : ℕ) : W))
    (hdb : ((R.endExtension j).equiv (domain b)).val ∈ range (j c))
    (hcof : ∀ d : W, ((R.endExtension j).equiv d).val ∈ range (j c) → ∃ p : W,
      functionFilterCandidate s (fun a ↦ ((R.endExtension j).equiv a).val ∈ range (j c))
        (fun x y ↦ (R.endExtension j).representedColor hg x = (R.endExtension j).representedColor hg y) b p ∧
          d ⊆ domain p) :
    ∃ m : W, ∀ p : W, p ∈ m ↔ functionFilterCandidate s
      (fun a ↦ ((R.endExtension j).equiv a).val ∈ range (j c))
      (fun x y ↦ (R.endExtension j).representedColor hg x = (R.endExtension j).representedColor hg y) b p := by
  let : IsOrdinal (j κ) := (j.ordinal_iff κ).mpr inferInstance
  have hc' := R.endExtension_finiteDomainChain j (R.equiv s).val (R.equiv s).property hc
  have hb' := ((R.endExtension j).selectedFunctionNode_iff s hc' b).mpr ⟨hb, hdb⟩
  have hcof' := (R.endExtension j).functionFilterCandidate_cofinality s hc' hg hb hcof
  have hpred := R.codedFunctionCandidate_predicate j s hc hRubin hpres hω hb' hweak hcof'
  let m := sep (finitePartialFunctions s ((2 : ℕ) : W))
    (fun p ↦ ((R.endExtension j).equiv p).val ∈
      codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g
        ((R.endExtension j).equiv b).val) hpred
  refine ⟨m, fun p ↦ ?_⟩
  have he := (R.endExtension j).functionFilterCandidate_iff s hc' hg (p := p) hb
  rw [R.endExtension_equiv_val j s] at he
  rw [show p ∈ m ↔ p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧
      ((R.endExtension j).equiv p).val ∈
        codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g
          ((R.endExtension j).equiv b).val from mem_sep_iff,
    ← he]
  exact ⟨And.right, fun hp ↦ ⟨hp.1, hp⟩⟩

end ZFVP.BinaryRelationRepresentation
