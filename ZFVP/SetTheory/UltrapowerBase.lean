import ZFVP.SetTheory.SetUltrafilter
import ZFVP.SetTheory.FunctionValue

/-! Almost everywhere relations on the functions from an index set into a rank stage, taken with
respect to a set ultrafilter on the index set. This is the first layer of the internal ultrapower:
the two relations, their defining separations, and the algebra of the ultrafilter that makes the
first one an equivalence and the second one compatible with it. No quotient and no Los theorem
here. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The functions from the index set `P` into the stage `A`. -/
noncomputable def ultraFunctions (P A : V) : V := A ^ P

@[simp] theorem mem_ultraFunctions_iff (P A f : V) : f ∈ ultraFunctions P A ↔ f ∈ A ^ P := Iff.rfl

instance ultraFunctions_definable : ℒₛₑₜ-function₂[V] ultraFunctions := by
  unfold ultraFunctions
  definability

/-- The index set on which two functions agree. -/
noncomputable def agreementSet (P f g : V) : V := {p ∈ P ; f ‘ p = g ‘ p}

/-- The index set on which one function's value belongs to the other's. -/
noncomputable def membershipSet (P f g : V) : V := {p ∈ P ; f ‘ p ∈ g ‘ p}

instance agreementSet_definable : ℒₛₑₜ-function₃[V] agreementSet := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y P f g ↦ ∀ p, p ∈ Y ↔ p ∈ P ∧ f ‘ p = g ‘ p) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = agreementSet (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [agreementSet, mem_sep_iff]

instance membershipSet_definable : ℒₛₑₜ-function₃[V] membershipSet := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y P f g ↦ ∀ p, p ∈ Y ↔ p ∈ P ∧ f ‘ p ∈ g ‘ p) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = membershipSet (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [membershipSet, mem_sep_iff]

@[simp] theorem mem_agreementSet_iff (P f g p : V) :
    p ∈ agreementSet P f g ↔ p ∈ P ∧ f ‘ p = g ‘ p := by simp [agreementSet]

@[simp] theorem mem_membershipSet_iff (P f g p : V) :
    p ∈ membershipSet P f g ↔ p ∈ P ∧ f ‘ p ∈ g ‘ p := by simp [membershipSet]

theorem agreementSet_subset (P f g : V) : agreementSet P f g ⊆ P := by
  intro p hp
  exact (mem_agreementSet_iff P f g p).mp hp |>.1

theorem membershipSet_subset (P f g : V) : membershipSet P f g ⊆ P := by
  intro p hp
  exact (mem_membershipSet_iff P f g p).mp hp |>.1

theorem agreementSet_self (P f : V) : agreementSet P f f = P := by
  apply mem_ext
  intro p
  simp [agreementSet]

/-- Equality almost everywhere with respect to `U`. -/
def AEEq (P U f g : V) : Prop := agreementSet P f g ∈ U

/-- Membership almost everywhere with respect to `U`. -/
def AEMem (P U f g : V) : Prop := membershipSet P f g ∈ U

instance aeEq_definable : ℒₛₑₜ-relation₄[V] AEEq := by
  unfold AEEq
  definability

instance aeMem_definable : ℒₛₑₜ-relation₄[V] AEMem := by
  unfold AEMem
  definability

variable {P U A X Y f f' g g' k : V}

theorem IsSetUltrafilter.index_mem (h : IsSetUltrafilter P U) : P ∈ U := h.2.1

theorem IsSetUltrafilter.empty_not_mem' (h : IsSetUltrafilter P U) : (∅ : V) ∉ U := h.2.2.1

theorem IsSetUltrafilter.mem_of_subset (h : IsSetUltrafilter P U) (hX : X ∈ U) (hXY : X ⊆ Y)
    (hY : Y ⊆ P) : Y ∈ U :=
  h.2.2.2.1 X hX Y hY hXY

theorem IsSetUltrafilter.inter_mem (h : IsSetUltrafilter P U) (hX : X ∈ U) (hY : Y ∈ U) :
    X ∩ Y ∈ U :=
  h.2.2.2.2.1 X hX Y hY

theorem IsSetUltrafilter.dichotomy' (h : IsSetUltrafilter P U) (hX : X ⊆ P) :
    X ∈ U ∨ relativeComplement P X ∈ U :=
  h.2.2.2.2.2 X hX

/-- A set in the ultrafilter meets every set in the ultrafilter, in particular it is nonempty
when the index set is. -/
theorem IsSetUltrafilter.isNonempty_of_mem (h : IsSetUltrafilter P U) (hX : X ∈ U) :
    IsNonempty X := by
  by_contra hno
  rw [not_isNonempty_iff_isEmpty] at hno
  have : X = (∅ : V) := by
    apply mem_ext
    intro z
    simp [hno.not_mem]
  exact h.empty_not_mem' (this ▸ hX)

/-- Exactly one of a subset of the index set and its relative complement is in the ultrafilter. -/
theorem IsSetUltrafilter.compl_mem_iff (h : IsSetUltrafilter P U) (hX : X ⊆ P) :
    relativeComplement P X ∈ U ↔ X ∉ U := by
  constructor
  · intro hc hXU
    obtain ⟨z, hz⟩ := (h.isNonempty_of_mem (h.inter_mem hXU hc)).nonempty
    rw [mem_inter_iff, mem_relativeComplement_iff] at hz
    exact hz.2.2 hz.1
  · intro hXU
    rcases h.dichotomy' hX with hin | hout
    · exact (hXU hin).elim
    · exact hout

theorem aeEq_refl (h : IsSetUltrafilter P U) : AEEq P U f f := by
  unfold AEEq
  rw [agreementSet_self]
  exact h.index_mem

theorem AEEq.symm (h : IsSetUltrafilter P U) (hfg : AEEq P U f g) : AEEq P U g f := by
  apply h.mem_of_subset hfg
  · intro p hp
    obtain ⟨hpP, hv⟩ := (mem_agreementSet_iff P f g p).mp hp
    exact (mem_agreementSet_iff P g f p).mpr ⟨hpP, hv.symm⟩
  · exact agreementSet_subset P g f

theorem AEEq.trans (h : IsSetUltrafilter P U) (hfg : AEEq P U f g) (hgk : AEEq P U g k) :
    AEEq P U f k := by
  apply h.mem_of_subset (h.inter_mem hfg hgk)
  · intro p hp
    rw [mem_inter_iff, mem_agreementSet_iff, mem_agreementSet_iff] at hp
    exact (mem_agreementSet_iff P f k p).mpr ⟨hp.1.1, hp.1.2.trans hp.2.2⟩
  · exact agreementSet_subset P f k

/-- Membership almost everywhere respects equality almost everywhere in both arguments. -/
theorem AEMem.congr (h : IsSetUltrafilter P U) (hff' : AEEq P U f f') (hgg' : AEEq P U g g')
    (hmem : AEMem P U f g) : AEMem P U f' g' := by
  apply h.mem_of_subset (h.inter_mem (h.inter_mem hff' hgg') hmem)
  · intro p hp
    rw [mem_inter_iff, mem_inter_iff, mem_agreementSet_iff, mem_agreementSet_iff,
      mem_membershipSet_iff] at hp
    refine (mem_membershipSet_iff P f' g' p).mpr ⟨hp.2.1, ?_⟩
    rw [← hp.1.1.2, ← hp.1.2.2]
    exact hp.2.2
  · exact membershipSet_subset P f' g'

/-- Almost everywhere, either the values agree or they do not. -/
theorem aeEq_or_not (h : IsSetUltrafilter P U) :
    AEEq P U f g ∨ relativeComplement P (agreementSet P f g) ∈ U :=
  h.dichotomy' (agreementSet_subset P f g)

theorem aeMem_or_not (h : IsSetUltrafilter P U) :
    AEMem P U f g ∨ relativeComplement P (membershipSet P f g) ∈ U :=
  h.dichotomy' (membershipSet_subset P f g)

end ZFVP
