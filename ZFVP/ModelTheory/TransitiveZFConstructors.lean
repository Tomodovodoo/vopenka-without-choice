import ZFVP.ModelTheory.TransitiveZFCoding

/-! Formula and assignment constructors commute with inclusion of a transitive ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem standardTuple_val {n : ℕ} (v : Fin n → SetDomain U) :
    (standardTuple v).val = standardTuple (fun i ↦ (v i).val) := by
  induction n with
  | zero => exact empty_val U
  | succ n ih =>
    change (assignmentPrepend (n : SetDomain U) (standardTuple (fun i ↦ v i.succ)) (v 0)).val =
      assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i.succ).val)) (v 0).val
    rw [assignmentPrepend_val U (by simp) ⟨inferInstance, domain_standardTuple _⟩,
      numeral_val U, ih]

theorem boundVarCode_val (i : SetDomain U) : (boundVarCode i).val = boundVarCode i.val := by
  simp only [boundVarCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, i.val⟩ₖ) (numeral_val U 0)

theorem relationToken_val (r : SetDomain U) : (relationToken r).val = relationToken r.val := by
  simp only [relationToken, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, r.val⟩ₖ) (numeral_val U 1)

theorem truthCode_val : (truthCode : SetDomain U).val = (truthCode : V) := by
  simp only [truthCode, kpair_val U, empty_val U]
  exact congrArg (fun z : V ↦ ⟨z, ∅⟩ₖ) (numeral_val U 0)

theorem falsityCode_val : (falsityCode : SetDomain U).val = (falsityCode : V) := by
  simp only [falsityCode, kpair_val U, empty_val U]
  exact congrArg (fun z : V ↦ ⟨z, ∅⟩ₖ) (numeral_val U 1)

theorem atomCode_val (r args : SetDomain U) : (atomCode r args).val = atomCode r.val args.val := by
  simp only [atomCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, ⟨r.val, args.val⟩ₖ⟩ₖ) (numeral_val U 2)

theorem negAtomCode_val (r args : SetDomain U) : (negAtomCode r args).val = negAtomCode r.val args.val := by
  simp only [negAtomCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, ⟨r.val, args.val⟩ₖ⟩ₖ) (numeral_val U 3)

theorem andCode_val (φ ψ : SetDomain U) : (andCode φ ψ).val = andCode φ.val ψ.val := by
  simp only [andCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, ⟨φ.val, ψ.val⟩ₖ⟩ₖ) (numeral_val U 4)

theorem orCode_val (φ ψ : SetDomain U) : (orCode φ ψ).val = orCode φ.val ψ.val := by
  simp only [orCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, ⟨φ.val, ψ.val⟩ₖ⟩ₖ) (numeral_val U 5)

theorem allCode_val (φ : SetDomain U) : (allCode φ).val = allCode φ.val := by
  simp only [allCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, φ.val⟩ₖ) (numeral_val U 6)

theorem existsCode_val (φ : SetDomain U) : (existsCode φ).val = existsCode φ.val := by
  simp only [existsCode, kpair_val U]
  exact congrArg (fun z : V ↦ ⟨z, φ.val⟩ₖ) (numeral_val U 7)

theorem boundedGuardArguments_val (i : SetDomain U) :
    (boundedGuardArguments i).val = boundedGuardArguments i.val := by
  unfold boundedGuardArguments
  rw [standardTuple_val U]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) j
  · exact (boundVarCode_val U _).trans (congrArg boundVarCode (numeral_val U 0))
  · exact (boundVarCode_val U _).trans (congrArg boundVarCode (succ_val U i))

theorem boundedAllCode_val (i φ : SetDomain U) :
    (boundedAllCode i φ).val = boundedAllCode i.val φ.val := by
  simp only [boundedAllCode, allCode_val U, orCode_val U, negAtomCode_val U,
    relationToken_val U, boundedGuardArguments_val U]
  exact congrArg (fun z : V ↦ allCode (orCode (negAtomCode (relationToken z)
    (boundedGuardArguments i.val)) φ.val)) (numeral_val U 1)

theorem boundedExistsCode_val (i φ : SetDomain U) :
    (boundedExistsCode i φ).val = boundedExistsCode i.val φ.val := by
  simp only [boundedExistsCode, existsCode_val U, andCode_val U, atomCode_val U,
    relationToken_val U, boundedGuardArguments_val U]
  exact congrArg (fun z : V ↦ existsCode (andCode (atomCode (relationToken z)
    (boundedGuardArguments i.val)) φ.val)) (numeral_val U 1)

theorem levyQuantifierCode_val (p : LevyPolarity) (φ : SetDomain U) :
    (levyQuantifierCode p φ).val = levyQuantifierCode p φ.val := by
  cases p
  · exact existsCode_val U φ
  · exact allCode_val U φ

end TransitiveZF

end ZFVP
