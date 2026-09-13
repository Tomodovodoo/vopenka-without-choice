import ZFVP.ModelTheory.InternalJointRealizationFormula
import ZFVP.ModelTheory.SchmerlCodedDirectedPosetFamily
import ZFVP.ModelTheory.SchmerlFiniteUpperBounds
import ZFVP.ModelTheory.RubinStage

/-! The actual coded directed posets have ordinary source formulas for their
domains and strict orders when ambient omega is standard. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedDefinableSet.exists_sourceFormula (hω : HasStandardOmega V)
    {D E P : V} (hD : IsNonempty D) (h : IsCodedDefinableSet (binaryRelationStructureCode D E) P) :
    ∃ δ : SetTheorySemiformula (BinaryRelationDomain D E) 1,
      ∀ x : BinaryRelationDomain D E, δ.Eval ![x] id ↔ x.val ∈ P := by
  obtain ⟨_, n, hn, φ, hφ, b, hb, hdef⟩ := h
  obtain ⟨n, rfl⟩ := hω n hn
  have hcode : IsMembershipFormulaCode ((n + 1 : ℕ) : V) φ := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hcode
  have hbD : b ∈ D ^ (n : V) := by simpa using hb
  obtain ⟨a, rfl⟩ := exists_binaryStandardTuple (R := E) hbD
  refine ⟨Rew.embSubsts (#0 :> fun t ↦ &(a t)) ▹ ψ, fun x ↦ ?_⟩
  have heval : (Rew.embSubsts (#0 :> fun t ↦ &(a t)) ▹ ψ).Eval ![x] id ↔
      ψ.Evalb (x :> a) := by
    simp only [Semiformula.eval_embSubsts]
    have hv : Semiterm.val (L := ℒₛₑₜ) ![x] id ∘ (#0 :> fun t ↦ &(a t)) = x :> a := by
      funext t
      refine Fin.cases ?_ (fun i ↦ ?_) t <;> simp
    rw [hv]
  rw [heval]
  have hh := (hψ D E hD (x :> a)).symm
  have hd := hdef x.val (by simpa using x.property)
  simpa only [codedSatisfies, num_succ_def] using hh.trans hd.symm

theorem IsCodedDefinableRelation.exists_sourceFormula (hω : HasStandardOmega V)
    {D E R : V} (hD : IsNonempty D) (h : IsCodedDefinableRelation (binaryRelationStructureCode D E) R) :
    ∃ ρ : SetTheorySemiformula (BinaryRelationDomain D E) 2,
      ∀ x y : BinaryRelationDomain D E, ρ.Eval ![x, y] id ↔ ⟨x.val, y.val⟩ₖ ∈ R := by
  obtain ⟨_, n, hn, φ, hφ, b, hb, hdef⟩ := h
  obtain ⟨n, rfl⟩ := hω n hn
  have hcode : IsMembershipFormulaCode ((n + 2 : ℕ) : V) φ := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hcode
  have hbD : b ∈ D ^ (n : V) := by simpa using hb
  obtain ⟨a, rfl⟩ := exists_binaryStandardTuple (R := E) hbD
  refine ⟨Rew.embSubsts (#0 :> #1 :> fun t ↦ &(a t)) ▹ ψ, fun x y ↦ ?_⟩
  have heval : (Rew.embSubsts (#0 :> #1 :> fun t ↦ &(a t)) ▹ ψ).Eval ![x, y] id ↔
      ψ.Evalb (x :> y :> a) := by
    simp only [Semiformula.eval_embSubsts]
    have hv : Semiterm.val (L := ℒₛₑₜ) ![x, y] id ∘ (#0 :> #1 :> fun t ↦ &(a t)) = x :> y :> a := by
      funext t
      refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) t <;> simp
    rw [hv]
  rw [heval]
  have hh := (hψ D E hD (x :> y :> a)).symm
  have hd := hdef x.val (by simpa using x.property) y.val (by simpa using y.property)
  simpa only [codedSatisfies, num_succ_def] using hh.trans hd.symm

theorem codedDirectedPoset_sourceFormulas (hω : HasStandardOmega V)
    {D E i : V} (hD : IsNonempty D) (hi : i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E)) :
    ∃ (δ : SetTheorySemiformula (BinaryRelationDomain D E) 1)
      (ρ : SetTheorySemiformula (BinaryRelationDomain D E) 2),
      (∀ x : BinaryRelationDomain D E, δ.Eval ![x] id ↔
        x.val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ i) ∧
      (∀ x y : BinaryRelationDomain D E, ρ.Eval ![x, y] id ↔
        ⟨x.val, y.val⟩ₖ ∈ (codedDirectedPosetRelations (binaryRelationStructureCode D E)) ‘ i ∧ x ≠ y) ∧
      DirectedNoLast (fun x ↦ δ.Eval ![x] id) (fun x y ↦ ρ.Eval ![x, y] id) := by
  obtain ⟨δ, hδ⟩ := (codedDirectedPosetFamily_definitions hi).1.exists_sourceFormula hω hD
  obtain ⟨ρ, hρ⟩ := (codedDirectedPosetFamily_definitions hi).2.exists_sourceFormula hω hD
  let σ : SetTheorySemiformula (BinaryRelationDomain D E) 2 := ρ ⋏ “#0 ≠ #1”
  have hσ (x y : BinaryRelationDomain D E) : σ.Eval ![x, y] id ↔
      ⟨x.val, y.val⟩ₖ ∈ (codedDirectedPosetRelations (binaryRelationStructureCode D E)) ‘ i ∧ x ≠ y := by
    simp [σ, hρ]
  have hpos := codedDirectedPosetFamily_poset hi
  have hdir := codedDirectedPosetFamily_directed hi
  have hsub : (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ i ⊆ D := by
    simpa only [binaryRelationStructureCode_domain] using
      mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem _) hi)
  refine ⟨δ, σ, hδ, hσ, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hdir.1
    exact ⟨⟨x, hsub x hx⟩, (hδ _).mpr hx⟩
  · intro x y z hx hy hz hxy hyz
    obtain ⟨hxy, hnxy⟩ := (hσ x y).mp hxy
    obtain ⟨hyz, hnyz⟩ := (hσ y z).mp hyz
    refine (hσ x z).mpr ⟨hpos.1.2.2 x.val ((hδ x).mp hx) y.val ((hδ y).mp hy)
      z.val ((hδ z).mp hz) hxy hyz, ?_⟩
    intro he
    apply hnxy
    apply Subtype.ext
    exact hpos.2 x.val ((hδ x).mp hx) y.val ((hδ y).mp hy) hxy (he ▸ hyz)
  · intro x y hx hy
    have hxP := (hδ x).mp hx
    have hyP := (hδ y).mp hy
    obtain ⟨w, hw, hxw, hyw⟩ := hdir.2.1 x.val hxP y.val hyP
    obtain ⟨z, hz, hwz, hne⟩ := hdir.strict_upper hw
    refine ⟨⟨z, hsub z hz⟩, (hδ _).mpr hz, (hσ _ _).mpr ⟨?_, ?_⟩, (hσ _ _).mpr ⟨?_, ?_⟩⟩
    · exact hpos.1.2.2 x.val hxP w hw z hz hxw hwz
    · intro he
      have he' : x.val = z := congrArg Subtype.val he
      exact hne (hpos.2 w hw z hz hwz (by rwa [← he']))
    · exact hpos.1.2.2 y.val hyP w hw z hz hyw hwz
    · intro he
      have he' : y.val = z := congrArg Subtype.val he
      exact hne (hpos.2 w hw z hz hwz (by rwa [← he']))

end ZFVP.Schmerl
