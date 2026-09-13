import ZFVP.ModelTheory.SchmerlCodedRankSelection
import ZFVP.ModelTheory.SchmerlCodedClassExpansion
import ZFVP.ModelTheory.SchmerlInternalBranchCore

/-! The specializing coloring takes natural values. The selected ordinal
chain embeds these colors into the original model's carrier, and an actual
total graph gives the added color relation on the whole carrier. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedClassColorValue (T c f x : V) : V := by
  classical
  exact if x ∈ T then c ‘ (f ‘ x) else c ‘ (0 : V)

instance codedClassColorValue_definable (T c f : V) : ℒₛₑₜ-function₁[V] (codedClassColorValue T c f) := by
  have h : ℒₛₑₜ-relation[V] (fun y x ↦
      (x ∈ T ∧ y = c ‘ (f ‘ x)) ∨ (x ∉ T ∧ y = c ‘ (0 : V))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = codedClassColorValue T c f (v 1) ↔ _
  unfold codedClassColorValue
  split <;> simp_all

noncomputable def codedClassColorGraph (D T c f : V) : V :=
  definableGraph D (codedClassColorValue T c f) (by definability)

theorem codedClassColorGraph_value {D T c f x : V} (hx : x ∈ D) :
    (codedClassColorGraph D T c f) ‘ x = codedClassColorValue T c f x :=
  value_definableGraph _ _ _ hx

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W)

noncomputable def representedColor {g : V} (hg : g ∈ R.carrier ^ R.carrier) (x : W) : W :=
  R.equiv.symm ⟨g ‘ (R.equiv x).val, function_value_mem hg (R.equiv x).property⟩

theorem representedColor_val {g : V} (hg : g ∈ R.carrier ^ R.carrier) (x : W) :
    (R.equiv (R.representedColor hg x)).val = g ‘ (R.equiv x).val :=
  congrArg (fun z : BinaryRelationDomain R.carrier R.relation ↦ z.val) (R.equiv.apply_symm_apply _)

theorem representedColor_eq_iff {g : V} (hg : g ∈ R.carrier ^ R.carrier) (x y : W) :
    R.representedColor hg x = R.representedColor hg y ↔ g ‘ (R.equiv x).val = g ‘ (R.equiv y).val := by
  rw [← R.equiv_val_injective.eq_iff, R.representedColor_val, R.representedColor_val]

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {c f : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hf : f ∈ (ω : V) ^ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)

include hc

theorem selectedClassNode_iff (t : ClassTreeNode W) :
    (R.equiv t.code).val ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c ↔
      (R.equiv t.level.val).val ∈ range c := by
  let : IsFunction c := IsFunction.of_mem hc.1
  rw [mem_codedSelectedClassNodes, and_iff_right (R.classNode_mem t), R.classLevels_value]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [he]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hc.1] using hi))
  · intro ht
    obtain ⟨i, hi⟩ := mem_range_iff.mp ht
    exact ⟨i, by simpa only [domain_eq_of_mem_function hc.1] using mem_domain_of_kpair_mem hi,
      (value_eq_of_kpair_mem hi).symm⟩

include hf

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] hc in
theorem codedClassColorValue_in_cover (x : V) :
    codedClassColorValue (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) c f x ∈
      repl (fun n : V ↦ c ‘ n) (by definability) (ω : V) := by
  unfold codedClassColorValue
  split_ifs with hx
  · exact (repl_spec (by definability)).mpr ⟨f ‘ x, function_value_mem hf hx, rfl⟩
  · exact (repl_spec (by definability)).mpr ⟨0, by simp, rfl⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codedClassColorGraph_function :
    codedClassColorGraph R.carrier (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) c f ∈
      R.carrier ^ R.carrier := by
  apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ _)
  intro y hy
  obtain ⟨x, _, rfl⟩ := (repl_spec (by definability)).mp hy
  obtain ⟨n, hn, he⟩ := (repl_spec (by definability)).mp (R.codedClassColorValue_in_cover hf x)
  rw [he]
  have hnκ : n ∈ hartogsNumber (ω : V) := IsOrdinal.toIsTransitive.mem_trans hn omega_mem_hartogs_omega
  have hnO := function_value_mem hc.1 hnκ
  obtain ⟨α, hα⟩ := (R.mem_ordinals_iff _).mp hnO
  rw [← hα]
  exact (R.equiv α.val).property

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codedClassColorGraph_not_Q :
    ¬R.representedQ (Set.range (R.representedColor (R.codedClassColorGraph_function hc hf))) := by
  intro hQ
  apply hQ
  refine ⟨repl (fun n : V ↦ c ‘ n) (by definability) (ω : V),
    internallyCountable_repl _ _ internallyCountable_omega, ?_⟩
  rintro y ⟨x, rfl⟩
  rw [R.representedColor_val, codedClassColorGraph_value (R.equiv x).property]
  exact R.codedClassColorValue_in_cover hf (R.equiv x).val

theorem codedClassColorGraph_internalWeak
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c) f) :
    InternallyWeakSpecialization (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c)
      (codedClassColorGraph R.carrier (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) c f) := by
  have hcarrier {x : V} (hx : x ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) : x ∈ R.carrier := by
    obtain ⟨t, rfl⟩ := (R.mem_classNodes_iff _).mp ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1
    exact (R.equiv t.code).property
  intro x hx y hy z hz hxy hxz hexy hexz
  have he {a b : V}
      (ha : a ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (hb : b ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (hab : (codedClassColorGraph R.carrier (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) c f) ‘ a =
        (codedClassColorGraph R.carrier (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) c f) ‘ b) :
      f ‘ a = f ‘ b := by
    rw [codedClassColorGraph_value (hcarrier ha), codedClassColorGraph_value (hcarrier hb)] at hab
    simp only [codedClassColorValue, ha, hb, ite_true] at hab
    exact hc.value_injective
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem hf ha) omega_mem_hartogs_omega)
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem hf hb) omega_mem_hartogs_omega) hab
  exact hweak x hx y hy z hz hxy hxz (he hx hy hexy) (he hx hz hexz)

theorem codedClassColorGraph_weak
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c) f) :
    ∀ x y z : ClassTreeNode W,
      (R.equiv x.level.val).val ∈ range c → (R.equiv y.level.val).val ∈ range c →
      (R.equiv z.level.val).val ∈ range c → x ≤ y → x ≤ z →
      R.representedColor (R.codedClassColorGraph_function hc hf) x.code =
        R.representedColor (R.codedClassColorGraph_function hc hf) y.code →
      R.representedColor (R.codedClassColorGraph_function hc hf) x.code =
        R.representedColor (R.codedClassColorGraph_function hc hf) z.code → y ≤ z ∨ z ≤ y := by
  intro x y z hx hy hz hxy hxz hexy hexz
  have hxT := (R.selectedClassNode_iff hc x).mpr hx
  have hyT := (R.selectedClassNode_iff hc y).mpr hy
  have hzT := (R.selectedClassNode_iff hc z).mpr hz
  have he {s t : ClassTreeNode W}
      (hs : (R.equiv s.code).val ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (ht : (R.equiv t.code).val ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (h : R.representedColor (R.codedClassColorGraph_function hc hf) s.code =
        R.representedColor (R.codedClassColorGraph_function hc hf) t.code) :
      f ‘ (R.equiv s.code).val = f ‘ (R.equiv t.code).val := by
    have hv := (R.representedColor_eq_iff (R.codedClassColorGraph_function hc hf) s.code t.code).mp h
    rw [codedClassColorGraph_value (R.equiv s.code).property,
      codedClassColorGraph_value (R.equiv t.code).property] at hv
    simp only [codedClassColorValue, hs, ht, ite_true] at hv
    exact hc.value_injective
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem hf hs) omega_mem_hartogs_omega)
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem hf ht) omega_mem_hartogs_omega) hv
  have h := hweak _ hxT _ hyT _ hzT
    ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨(R.classOrder_iff x y).mpr hxy, hxT, hyT⟩)
    ((pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨(R.classOrder_iff x z).mpr hxz, hxT, hzT⟩)
    (he hxT hyT hexy) (he hxT hzT hexz)
  exact h.imp (fun h ↦ (R.classOrder_iff y z).mp (mem_inter_iff.mp h).1)
    (fun h ↦ (R.classOrder_iff z y).mp (mem_inter_iff.mp h).1)

end ZFVP.BinaryRelationRepresentation
