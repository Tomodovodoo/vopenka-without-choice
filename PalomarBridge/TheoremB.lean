import PalomarBridge.VPDictionary
import ZFVP.ModelTheory.WoodinSparseRestorationTheorem

/-!
Theorem B with a complete independent membership-language statement.

The intermediate translated theories preserve the exact source dictionaries.
The ZF, AC, and VP correspondence lemmas then eliminate those source-dependent
values from the final theorem statement. `independent_theoremB` has no extra
hypotheses and its type uses only the independent vocabulary.
-/

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The existing ZF+VP dictionary transported without changing any axiom. -/
def translatedZFVP : PalomarBridge.Theory := translateTheory ZFVP.zfVPTheory

/-- The existing ZFC+VP dictionary transported without changing any axiom. -/
def translatedZFCVP : PalomarBridge.Theory := translateTheory ZFVP.zfcVPTheory

/-- The transported theory has a model exactly when the source is consistent. -/
theorem translatedZFVP_satisfiable_iff :
    PalomarBridge.Satisfiable translatedZFVP ↔ Entailment.Consistent ZFVP.zfVPTheory :=
  satisfiable_translateTheory_iff _ (fun p hp =>
    Or.inl (ZermeloFraenkel.axiom_of_equality p hp))

/-- The transported choice theory has a model exactly when the source is consistent. -/
theorem translatedZFCVP_satisfiable_iff :
    PalomarBridge.Satisfiable translatedZFCVP ↔ Entailment.Consistent ZFVP.zfcVPTheory :=
  satisfiable_translateTheory_iff _ (fun p hp =>
    Or.inl (Or.inl (ZermeloFraenkel.axiom_of_equality p hp)))

/-- Theorem B expressed as model existence in independent membership syntax.
The final theorem below replaces the two translated theory values by the
proved independent ZF, AC, and VP definitions.
Neither value is left opaque or supplied as a free parameter here. -/
theorem theoremB_transported :
    PalomarBridge.Satisfiable translatedZFCVP ↔ PalomarBridge.Satisfiable translatedZFVP :=
  translatedZFCVP_satisfiable_iff.trans
    (ZFVP.consistent_zfcVP_iff_consistent_zfVP_woodin.trans translatedZFVP_satisfiable_iff.symm)

/-- The translated VP theory used in the intermediate model equivalences. -/
def translatedVP : PalomarBridge.Theory := translateTheory ZFVP.vopenkaTheory

variable {M : Type} [SetStructure M] [Nonempty M]

theorem independentZF_with_translatedVP_iff :
    IsZF (fun x y : M => x ∈ y) ∧ Models (fun x y : M => x ∈ y) translatedVP ↔
    M↓[ℒₛₑₜ] ⊧* ZFVP.zfVPTheory := by
  rw [isZF_iff_models, translatedVP, models_translateTheory_iff]
  simp [ZFVP.zfVPTheory, models_theory_iff]

theorem independentZFC_with_translatedVP_iff :
    IsZF (fun x y : M => x ∈ y) ∧ HasChoice (fun x y : M => x ∈ y) ∧
      Models (fun x y : M => x ∈ y) translatedVP ↔
    M↓[ℒₛₑₜ] ⊧* ZFVP.zfcVPTheory := by
  rw [isZF_iff_models, hasChoice_iff_models, translatedVP, models_translateTheory_iff]
  simp [ZFVP.zfcVPTheory, ZermeloFraenkelChoice, models_theory_iff, and_assoc]

/-- Theorem B with independent ZF and AC definitions. This intermediate statement
retains the translated VP theory; the final theorem below removes it. -/
theorem theoremB_independentZF :
    (∃ (M : Type) (mem : M → M → Prop),
      IsZF mem ∧ HasChoice mem ∧ Models mem translatedVP) ↔
    (∃ (M : Type) (mem : M → M → Prop), IsZF mem ∧ Models mem translatedVP) := by
  have left :
      (∃ (M : Type) (mem : M → M → Prop),
        IsZF mem ∧ HasChoice mem ∧ Models mem translatedVP) ↔
      PalomarBridge.Satisfiable translatedZFCVP := by
    constructor
    · rintro ⟨M, mem, hzf, hac, hvp⟩
      let : SetStructure M := ⟨fun y x => mem x y⟩
      let : Nonempty M := hzf.inhabited
      exact ⟨M, mem, (models_translateTheory_iff _).mpr
        (independentZFC_with_translatedVP_iff.mp ⟨hzf, hac, hvp⟩)⟩
    · rintro ⟨M, mem, hm⟩
      let : SetStructure M := ⟨fun y x => mem x y⟩
      let : Nonempty M := hm.1
      exact ⟨M, mem, independentZFC_with_translatedVP_iff.mpr
        ((models_translateTheory_iff _).mp hm)⟩
  have right :
      (∃ (M : Type) (mem : M → M → Prop), IsZF mem ∧ Models mem translatedVP) ↔
      PalomarBridge.Satisfiable translatedZFVP := by
    constructor
    · rintro ⟨M, mem, hzf, hvp⟩
      let : SetStructure M := ⟨fun y x => mem x y⟩
      let : Nonempty M := hzf.inhabited
      exact ⟨M, mem, (models_translateTheory_iff _).mpr
        (independentZF_with_translatedVP_iff.mp ⟨hzf, hvp⟩)⟩
    · rintro ⟨M, mem, hm⟩
      let : SetStructure M := ⟨fun y x => mem x y⟩
      let : Nonempty M := hm.1
      exact ⟨M, mem, independentZF_with_translatedVP_iff.mpr
        ((models_translateTheory_iff _).mp hm)⟩
  exact left.trans (theoremB_transported.trans right.symm)

/-- Exact identification of the independent VP scheme with the original theory. -/
theorem coding_vopenka_iff_models [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    Coding.Vopenka (fun x y : M => x ∈ y) ↔ M↓[ℒₛₑₜ] ⊧* ZFVP.vopenkaTheory := by
  rw [coding_vopenka_iff]
  simp [ZFVP.vopenkaTheory, ZFVP.eval_vopenkaSentence]

/-- The independent model statement has exactly the source consistency strength. -/
theorem hasZFVPModel_iff_consistent :
    HasZFVPModel ↔ Entailment.Consistent ZFVP.zfVPTheory := by
  rw [← translatedZFVP_satisfiable_iff]
  constructor
  · rintro ⟨M, mem, hne, hzf, hvp⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hne
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    have hv : Models mem translatedVP :=
      (models_translateTheory_iff _).mpr (coding_vopenka_iff_models.mp hvp)
    exact ⟨M, mem, (models_translateTheory_iff _).mpr
      (independentZF_with_translatedVP_iff.mp ⟨hzf, hv⟩)⟩
  · rintro ⟨M, mem, hm⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hm.1
    obtain ⟨hzf, hvp⟩ := independentZF_with_translatedVP_iff.mpr
      ((models_translateTheory_iff _).mp hm)
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    exact ⟨M, mem, hm.1, hzf, coding_vopenka_iff_models.mpr
      ((models_translateTheory_iff _).mp hvp)⟩

/-- The independent choice-model statement has exactly the source consistency strength. -/
theorem hasZFCVPModel_iff_consistent :
    HasZFCVPModel ↔ Entailment.Consistent ZFVP.zfcVPTheory := by
  rw [← translatedZFCVP_satisfiable_iff]
  constructor
  · rintro ⟨M, mem, hne, hzf, hac, hvp⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hne
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    have hv : Models mem translatedVP :=
      (models_translateTheory_iff _).mpr (coding_vopenka_iff_models.mp hvp)
    exact ⟨M, mem, (models_translateTheory_iff _).mpr
      (independentZFC_with_translatedVP_iff.mp ⟨hzf, hac, hv⟩)⟩
  · rintro ⟨M, mem, hm⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hm.1
    obtain ⟨hzf, hac, hvp⟩ := independentZFC_with_translatedVP_iff.mpr
      ((models_translateTheory_iff _).mp hm)
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    exact ⟨M, mem, hm.1, hzf, hac, coding_vopenka_iff_models.mpr
      ((models_translateTheory_iff _).mp hvp)⟩

/-- Theorem B with a complete independent statement and no extra hypotheses.
By the proved completeness equivalences, this is Con(ZFC+VP) iff Con(ZF+VP). -/
theorem independent_theoremB : HasZFCVPModel ↔ HasZFVPModel :=
  hasZFCVPModel_iff_consistent.trans
    (ZFVP.consistent_zfcVP_iff_consistent_zfVP_woodin.trans hasZFVPModel_iff_consistent.symm)

end PalomarBridge

#print axioms PalomarBridge.independent_theoremB







