import ZFVP.Syntax.BinaryRelationInternalSemantics
import ZFVP.ModelTheory.SchmerlStandardOmega

/-! Decoding internal membership formulas up to truth in arbitrary binary
relation structures. Raw logical equality and relation-symbol equality are
allowed to decode to the same external equality formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def BinaryFormulaRepresents {k : ℕ} (φ : V) (ψ : SetTheorySemisentence k) : Prop :=
  ∀ (D E : V), IsNonempty D → ∀ b : Fin k → BinaryRelationDomain D E,
    Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ (k : V) φ
      (standardTuple (fun i ↦ (b i).val)) ↔ ψ.Evalb b

namespace BinaryFormulaRepresents

theorem encoded {k : ℕ} (ψ : SetTheorySemisentence k) :
    BinaryFormulaRepresents (V := V) (encodeMembershipFormula ψ) ψ :=
  fun _ _ hD b ↦ satisfies_encodeBinaryRelationFormula hD ψ b

theorem truth (k : ℕ) : BinaryFormulaRepresents (V := V) truthCode (⊤ : SetTheorySemisentence k) := by
  intro D E _ b
  exact iff_of_true ((satisfies_truth membershipLanguageCode_valid (by simp)).mpr
    (by simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function _ (fun i ↦ (b i).property))) (by simp)

theorem falsity (k : ℕ) : BinaryFormulaRepresents (V := V) falsityCode (⊥ : SetTheorySemisentence k) := by
  intro D E _ b
  exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid (by simp)) (by simp)

theorem conj {k : ℕ} {φ χ : V} {ψ θ : SetTheorySemisentence k}
    (hφ : IsMembershipFormulaCode (k : V) φ) (hχ : IsMembershipFormulaCode (k : V) χ)
    (hψ : BinaryFormulaRepresents φ ψ) (hθ : BinaryFormulaRepresents χ θ) :
    BinaryFormulaRepresents (andCode φ χ) (ψ ⋏ θ) := by
  intro D E hD b
  exact (satisfies_and membershipLanguageCode_valid (by simp) hφ.valid hχ.valid
    (by simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function _ (fun i ↦ (b i).property))).trans
        (and_congr (hψ D E hD b) (hθ D E hD b))

theorem disj {k : ℕ} {φ χ : V} {ψ θ : SetTheorySemisentence k}
    (hφ : IsMembershipFormulaCode (k : V) φ) (hχ : IsMembershipFormulaCode (k : V) χ)
    (hψ : BinaryFormulaRepresents φ ψ) (hθ : BinaryFormulaRepresents χ θ) :
    BinaryFormulaRepresents (orCode φ χ) (ψ ⋎ θ) := by
  intro D E hD b
  exact (satisfies_or membershipLanguageCode_valid (by simp) hφ.valid hχ.valid
    (by simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function _ (fun i ↦ (b i).property))).trans
        (or_congr (hψ D E hD b) (hθ D E hD b))

theorem all {k : ℕ} {φ : V} {ψ : SetTheorySemisentence (k + 1)}
    (hφ : IsMembershipFormulaCode ((k + 1 : ℕ) : V) φ) (hψ : BinaryFormulaRepresents φ ψ) :
    BinaryFormulaRepresents (allCode φ) (∀¹ ψ) := by
  intro D E hD b
  have hφ' : φ ∈ formulaSet membershipLanguageCode ∅ (succ (k : V)) := by
    simpa only [num_succ_def] using hφ.valid
  rw [satisfies_all membershipLanguageCode_valid (by simp) hφ'
    (by simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function _ (fun i ↦ (b i).property)), binaryRelationStructureCode_domain]
  change (∀ x : V, x ∈ D → _) ↔ ∀ x : BinaryRelationDomain D E, ψ.Evalb (x :> b)
  constructor
  · intro h x
    apply (hψ D E hD (x :> b)).mp
    simpa only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, num_succ_def] using h x.val x.property
  · intro h x hx
    let x' : BinaryRelationDomain D E := ⟨x, hx⟩
    have he := (hψ D E hD (x' :> b)).mpr (h x')
    have he' : Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅
        (succ (k : V)) φ (assignmentPrepend (k : V) (standardTuple (fun i ↦ (b i).val)) x'.val) := by
      simpa only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, num_succ_def] using he
    exact he'

theorem exs {k : ℕ} {φ : V} {ψ : SetTheorySemisentence (k + 1)}
    (hφ : IsMembershipFormulaCode ((k + 1 : ℕ) : V) φ) (hψ : BinaryFormulaRepresents φ ψ) :
    BinaryFormulaRepresents (existsCode φ) (∃¹ ψ) := by
  intro D E hD b
  have hφ' : φ ∈ formulaSet membershipLanguageCode ∅ (succ (k : V)) := by
    simpa only [num_succ_def] using hφ.valid
  rw [satisfies_exists membershipLanguageCode_valid (by simp) hφ'
    (by simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function _ (fun i ↦ (b i).property)), binaryRelationStructureCode_domain]
  change (∃ x : V, x ∈ D ∧ _) ↔ ∃ x : BinaryRelationDomain D E, ψ.Evalb (x :> b)
  constructor
  · rintro ⟨x, hx, ht⟩
    let x' : BinaryRelationDomain D E := ⟨x, hx⟩
    refine ⟨x', (hψ D E hD (x' :> b)).mp ?_⟩
    have ht' : Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅
        (succ (k : V)) φ (assignmentPrepend (k : V) (standardTuple (fun i ↦ (b i).val)) x'.val) := ht
    simpa only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, num_succ_def] using ht'
  · rintro ⟨x, hx⟩
    refine ⟨x.val, x.property, ?_⟩
    have he := (hψ D E hD (x :> b)).mpr hx
    simpa only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, num_succ_def] using he

end BinaryFormulaRepresents

theorem binary_atoms_representable {k : ℕ} {r args : V}
    (ha : IsAtomicArguments membershipLanguageCode ∅ (k : V) r args) :
    ∃ ψ : SetTheorySemisentence k,
      BinaryFormulaRepresents (atomCode r args) ψ ∧ BinaryFormulaRepresents (negAtomCode r args) (∼ψ) := by
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff (by simp)).mp ha
  obtain ⟨i, rfl⟩ := (mem_natCast_iff i k).mp hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff j k).mp hj
  have hbase : ∃ ψ : SetTheorySemisentence k, ∀ (D E : V), IsNonempty D →
      ∀ b : Fin k → BinaryRelationDomain D E,
        AtomicHolds membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ (k : V)
          (standardTuple (fun l ↦ (b l).val)) r (boundPairArguments (i.val : V) (j.val : V)) ↔ ψ.Evalb b := by
    rcases hr with rfl | rfl | rfl
    · refine ⟨.rel Language.Set.Rel.eq ![.bvar i, .bvar j], fun D E _ b ↦ ?_⟩
      rw [binaryAtomic_logicalEquality (by simp) (natCast_mem_of_lt i.isLt) (natCast_mem_of_lt j.isLt),
        value_standardTuple, value_standardTuple]
      exact Subtype.val_injective.eq_iff
    · refine ⟨.rel Language.Set.Rel.eq ![.bvar i, .bvar j], fun D E _ b ↦ ?_⟩
      rw [binaryAtomic_relationEquality (by simp) (natCast_mem_of_lt i.isLt) (natCast_mem_of_lt j.isLt)
        (standardTuple_mem_function _ (fun l ↦ (b l).property)), value_standardTuple, value_standardTuple]
      exact Subtype.val_injective.eq_iff
    · refine ⟨.rel Language.Set.Rel.mem ![.bvar i, .bvar j], fun D E _ b ↦ ?_⟩
      rw [binaryAtomic_membership (by simp) (natCast_mem_of_lt i.isLt) (natCast_mem_of_lt j.isLt)
        (standardTuple_mem_function _ (fun l ↦ (b l).property)), value_standardTuple, value_standardTuple]
      rfl
  obtain ⟨ψ, hψ⟩ := hbase
  refine ⟨ψ, ?_, ?_⟩
  · intro D E hD b
    exact (satisfies_atom membershipLanguageCode_valid (by simp) ha
      (by simpa only [binaryRelationStructureCode_domain] using
        standardTuple_mem_function _ (fun l ↦ (b l).property))).trans (hψ D E hD b)
  · intro D E hD b
    have he := (satisfies_negAtom membershipLanguageCode_valid (by simp) ha
      (by simpa only [binaryRelationStructureCode_domain] using
        standardTuple_mem_function _ (fun l ↦ (b l).property))).trans (not_congr (hψ D E hD b))
    simpa [Semiformula.Evalb] using he

/-- External well-foundedness is used only to decode finite syntax. The
represented binary relation itself may be ill founded. -/
theorem binary_formula_representable_of_wellFounded
    (hV : WellFounded (fun x y : V ↦ x ∈ y)) {k : ℕ} {φ : V}
    (hφ : IsMembershipFormulaCode (k : V) φ) :
    ∃ ψ : SetTheorySemisentence k, BinaryFormulaRepresents φ ψ := by
  have hw : WellFounded (fun x y : V ↦ rank x ∈ rank y) := InvImage.wf rank hV
  induction φ using hw.induction generalizing k with
  | h φ ih =>
    rcases formulaSet_cases membershipLanguageCode_valid hφ.valid with
      rfl | rfl | ⟨r, args, ha, he⟩ | ⟨χ, θ, hχ, hθ, he⟩ | ⟨χ, hχ, he⟩
    · exact ⟨⊤, BinaryFormulaRepresents.truth k⟩
    · exact ⟨⊥, BinaryFormulaRepresents.falsity k⟩
    · obtain ⟨ψ, hp, hn⟩ := binary_atoms_representable ha
      rcases he with rfl | rfl
      · exact ⟨ψ, hp⟩
      · exact ⟨∼ψ, hn⟩
    · have hc : IsMembershipFormulaCode (k : V) χ := (mem_formulaSet_iff _ _ _ _).mp hχ
      have ht : IsMembershipFormulaCode (k : V) θ := (mem_formulaSet_iff _ _ _ _).mp hθ
      have hχφ : rank χ ∈ rank φ := by
        rcases he with rfl | rfl
        · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt χ θ) (rank_kpair_right_lt (4 : V) _)
        · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt χ θ) (rank_kpair_right_lt (5 : V) _)
      have hθφ : rank θ ∈ rank φ := by
        rcases he with rfl | rfl
        · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt χ θ) (rank_kpair_right_lt (4 : V) _)
        · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt χ θ) (rank_kpair_right_lt (5 : V) _)
      obtain ⟨ψ, hψ⟩ := ih χ hχφ hc
      obtain ⟨ρ, hρ⟩ := ih θ hθφ ht
      rcases he with rfl | rfl
      · exact ⟨ψ ⋏ ρ, hψ.conj hc ht hρ⟩
      · exact ⟨ψ ⋎ ρ, hψ.disj hc ht hρ⟩
    · have hc : IsMembershipFormulaCode ((k + 1 : ℕ) : V) χ := by
        simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hχ
      have hχφ : rank χ ∈ rank φ := by
        rcases he with rfl | rfl
        · exact rank_kpair_right_lt (6 : V) χ
        · exact rank_kpair_right_lt (7 : V) χ
      obtain ⟨ψ, hψ⟩ := ih χ hχφ hc
      rcases he with rfl | rfl
      · exact ⟨∀¹ ψ, hψ.all hc⟩
      · exact ⟨∃¹ ψ, hψ.exs hc⟩

/-- Semantic coverage of all internal membership syntax. Unlike exact
encoding surjectivity, this permits both internal equality encodings. -/
structure SemanticStandardMembershipSyntax (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop where
  naturals : Schmerl.HasStandardOmega V
  formulas : ∀ (k : ℕ) (φ : V), IsMembershipFormulaCode (k : V) φ →
    ∃ ψ : SetTheorySemisentence k, BinaryFormulaRepresents φ ψ

theorem semanticStandardMembershipSyntax_of_wellFounded
    (hV : WellFounded (fun x y : V ↦ x ∈ y)) : SemanticStandardMembershipSyntax V :=
  ⟨Schmerl.standardOmega_of_wellFounded hV, fun _ _ hφ ↦ binary_formula_representable_of_wellFounded hV hφ⟩

theorem universe_semanticStandardMembershipSyntax : SemanticStandardMembershipSyntax Universe.{u} :=
  semanticStandardMembershipSyntax_of_wellFounded Universe.wellFounded

end ZFVP
