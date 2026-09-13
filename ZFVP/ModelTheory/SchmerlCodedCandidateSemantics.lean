import ZFVP.ModelTheory.SchmerlCodedCandidatePreservation
import ZFVP.ModelTheory.SchmerlInfinitaryClassWithQ

/-! Identify exactly the candidates quantified by the fixed class sentence.
Their syntactic cofinality test yields the internal cofinality premise used by
branch preservation. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open ZFVP.Infinitary (Formula)

def classCandidateFormula : Formula classLanguage 2 :=
  canonicalBranchCandidate (classOriginal classNodeFormula)
    (selectedRankNodes classSelected (classOriginal classRankFormula))
    (classOriginal classOrderFormula) (equalityOfColors classColor)

noncomputable def classBranchClause : Formula classLanguage 0 :=
  branchDefinabilityClause classLanguageEmbedding (classOriginal classNodeFormula)
    (selectedRankNodes classSelected (classOriginal classRankFormula)) (classOriginal ordinalNodeFormula)
    (classOriginal classOrderFormula) (equalityOfColors classColor)
    (nodeRankAbove (classOriginal classRankFormula) (classOriginal ordinalOrderFormula))

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)
variable {c g : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hg : g ∈ R.carrier ^ R.carrier)

@[instance_reducible] noncomputable def representedClassExpansion (c : V) : Structure classLanguage W :=
  classExpansion (fun x ↦ (R.equiv x).val ∈ range c) (R.representedColor hg)

include hc

theorem eval_selectedClassNode (t : ClassTreeNode W) :
    @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 1
      (selectedRankNodes classSelected (classOriginal classRankFormula)) ![t.code] ↔
      (R.equiv t.code).val ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c := by
  let D := fun x ↦ (R.equiv x).val ∈ range c
  let f := R.representedColor hg
  let : Structure classLanguage W := classExpansion D f
  have hJ (a : W) : (classOriginal classRankFormula).Eval ![t.code, a] ↔ a = t.level.val :=
    (eval_classOriginal D f classRankFormula ![t.code, a]).trans (eval_classRankFormula t a)
  rw [R.selectedClassNode_iff hc t]
  simp only [eval_selectedRankNodes, hJ, eval_classSelected]
  exact ⟨fun ⟨a, ha, he⟩ ↦ he ▸ ha, fun hx ↦ ⟨t.level.val, hx, rfl⟩⟩

theorem eval_classCandidate (x b : W) :
    @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 2 classCandidateFormula ![x, b] ↔
      (R.equiv x).val ∈ codedClassCandidate R.code (hartogsNumber (ω : V)) c g (R.equiv b).val := by
  let D := fun x ↦ (R.equiv x).val ∈ range c
  let f := R.representedColor hg
  let : Structure classLanguage W := classExpansion D f
  have hN (x : W) : (classOriginal classNodeFormula).Eval ![x] ↔ x ∈ Set.range (ClassTreeNode.code (V := W)) :=
    (eval_classOriginal D f classNodeFormula ![x]).trans (eval_classNodeFormula x)
  have hr (x y : ClassTreeNode W) : (classOriginal classOrderFormula).Eval ![x.code, y.code] ↔
      ⟨(R.equiv x.code).val, (R.equiv y.code).val⟩ₖ ∈ codedClassOrder R.code :=
    ((eval_classOriginal D f classOrderFormula ![x.code, y.code]).trans
      (eval_classOrderFormula x y)).trans (R.classOrder_iff x y).symm
  have hE (x y : W) : (equalityOfColors classColor).Eval ![x, y] ↔
      g ‘ (R.equiv x).val = g ‘ (R.equiv y).val := by
    have he : (equalityOfColors classColor).Eval ![x, y] ↔ f x = f y := by
      simp [eval_equalityOfColors, eval_classColor]
    exact he.trans (R.representedColor_eq_iff hg x y)
  rw [classCandidateFormula, eval_canonicalBranchCandidate, mem_codedClassCandidate]
  constructor
  · rintro ⟨hx, hb, y, hy, hdy, hcone, hxy⟩
    obtain ⟨x, rfl⟩ := (hN x).mp hx
    obtain ⟨b, rfl⟩ := (hN b).mp hb
    obtain ⟨y, rfl⟩ := (hN y).mp hy
    exact ⟨R.classNode_mem x, R.classNode_mem b, (R.equiv y.code).val,
      (R.eval_selectedClassNode hc hg y).mp hdy,
      (or_congr (hr y b) (and_congr (hr b y) (hE b.code y.code))).mp hcone, (hr x y).mp hxy⟩
  · rintro ⟨hx, hb, y, hy, hcone, hxy⟩
    obtain ⟨xt, hxt⟩ := (R.mem_classNodes_iff _).mp hx
    have hxe : xt.code = x := R.equiv_val_injective hxt
    obtain ⟨bt, hbt⟩ := (R.mem_classNodes_iff _).mp hb
    have hbe : bt.code = b := R.equiv_val_injective hbt
    obtain ⟨yt, hyt⟩ := (R.mem_classNodes_iff _).mp ((mem_codedSelectedClassNodes _ _ _ _).mp hy).1
    subst x
    subst b
    rw [← hyt] at hy hcone hxy
    exact ⟨(hN xt.code).mpr ⟨xt, rfl⟩, (hN bt.code).mpr ⟨bt, rfl⟩,
      yt.code, (hN yt.code).mpr ⟨yt, rfl⟩, (R.eval_selectedClassNode hc hg yt).mpr hy,
      (or_congr (hr yt bt) (and_congr (hr bt yt) (hE bt.code yt.code))).mpr hcone, (hr xt yt).mpr hxy⟩

theorem classCandidate_cofinality {b : W}
    (hcof : ∀ a : W,
      @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 1 (classOriginal ordinalNodeFormula) ![a] →
      ∃ x : W, @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 2 classCandidateFormula ![x, b] ∧
        @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 2
          (nodeRankAbove (classOriginal classRankFormula) (classOriginal ordinalOrderFormula)) ![x, a]) :
    ∀ i ∈ hartogsNumber (ω : V), ∃ x ∈ codedClassCandidate R.code (hartogsNumber (ω : V)) c g (R.equiv b).val,
      ⟨c ‘ i, (codedClassLevels R.code) ‘ x⟩ₖ ∈ codedOrdinalOrder R.code := by
  let D := fun x ↦ (R.equiv x).val ∈ range c
  let f := R.representedColor hg
  let : Structure classLanguage W := classExpansion D f
  intro i hi
  obtain ⟨a, ha⟩ := (R.mem_ordinals_iff _).mp (function_value_mem hc.1 hi)
  have haO : (classOriginal ordinalNodeFormula).Eval ![a.val] :=
    (eval_classOriginal D f ordinalNodeFormula ![a.val]).mpr
      ((eval_ordinalNodeFormula a.val).mpr ⟨a, rfl⟩)
  obtain ⟨x, hx, hax⟩ := hcof a.val haO
  have hxC := (R.eval_classCandidate hc hg x b).mp hx
  obtain ⟨t, ht⟩ := (R.mem_classNodes_iff _).mp ((mem_codedClassCandidate _ _ _ _ _ _).mp hxC).1
  have htx : t.code = x := R.equiv_val_injective ht
  subst x
  refine ⟨(R.equiv t.code).val, hxC, ?_⟩
  rw [R.classLevels_value, ← ha]
  apply (R.ordinalOrder_iff a t.level).mpr
  obtain ⟨z, hz, haz⟩ := (eval_nodeRankAbove _ _ _ _).mp hax
  have hz' := (eval_classRankFormula t z).mp ((eval_classOriginal D f classRankFormula _).mp hz)
  subst z
  exact (eval_ordinalOrderFormula a t.level).mp ((eval_classOriginal D f ordinalOrderFormula _).mp haz)

end ZFVP.BinaryRelationRepresentation
