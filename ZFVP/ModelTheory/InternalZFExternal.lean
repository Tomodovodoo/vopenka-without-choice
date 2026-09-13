import ZFVP.ModelTheory.InternalZFModel
import ZFVP.Syntax.CloseParameters

/-! Every internally coded ZF model satisfies all external ZF axiom instances. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem standardTuple_cast {m n : ℕ} (h : m = n) (v : Fin n → V) :
    standardTuple (v ∘ Fin.cast h) = standardTuple v := by
  subst n
  rfl

theorem membershipSatisfies_closeParameters {A : V} (hA : IsNonempty A)
    [Nonempty (SetDomain A)] {n : ℕ} (φ : SetTheorySemiproposition (n + 1))
    (b : Fin (n + 1) → SetDomain A) (e : ℕ → SetDomain A) :
    MembershipSatisfies A (((n + 1) + φ.fvSup : ℕ) : V) (encodeMembershipFormula (closeParameters φ))
      (standardTuple (fun i ↦ (Fin.append b (fun j : Fin φ.fvSup ↦ e j.val) i).val)) ↔
      φ.Eval b e :=
  (membershipSatisfies_encode hA (closeParameters φ) _).trans (eval_closeParameters φ b e)

theorem membershipSatisfies_closeParameters_one {A : V} (hA : IsNonempty A)
    [Nonempty (SetDomain A)] (φ : SetTheorySemiproposition 1)
    (x : SetDomain A) (e : ℕ → SetDomain A) :
    MembershipSatisfies A (succ (φ.fvSup : V)) (encodeMembershipFormula (closeParameters φ))
      (assignmentPrepend (φ.fvSup : V) (standardTuple (fun i : Fin φ.fvSup ↦ (e i.val).val)) x.val) ↔
      φ.Eval ![x] e := by
  have h := membershipSatisfies_closeParameters hA φ ![x] e
  rw [Fin.append_left_eq_cons] at h
  have ht : (fun i ↦ ((Fin.cons x (fun j : Fin φ.fvSup ↦ e j.val) ∘
      Fin.cast (Nat.add_comm 1 φ.fvSup)) i).val) =
      (Fin.cons x.val (fun j : Fin φ.fvSup ↦ (e j.val).val)) ∘
        Fin.cast (Nat.add_comm 1 φ.fvSup) := by
    funext i
    simp only [Function.comp_apply]
    exact Fin.cases rfl (fun _ ↦ rfl) (Fin.cast (Nat.add_comm 1 φ.fvSup) i)
  rw [show (![x] : Fin 1 → SetDomain A) 0 = x from rfl, ht, standardTuple_cast] at h
  simpa [Nat.add_comm 1, num_succ_def, standardTuple] using h

theorem membershipSatisfies_closeParameters_two {A : V} (hA : IsNonempty A)
    [Nonempty (SetDomain A)] (φ : SetTheorySemiproposition 2)
    (x y : SetDomain A) (e : ℕ → SetDomain A) :
    MembershipSatisfies A (succ (succ (φ.fvSup : V))) (encodeMembershipFormula (closeParameters φ))
      (assignmentPrepend (succ (φ.fvSup : V))
        (assignmentPrepend (φ.fvSup : V) (standardTuple (fun i : Fin φ.fvSup ↦ (e i.val).val)) y.val) x.val) ↔
      φ.Eval ![x, y] e := by
  have h := membershipSatisfies_closeParameters hA φ ![x, y] e
  have ht : (fun i ↦ (Fin.append ![x, y] (fun j : Fin φ.fvSup ↦ e j.val) i).val) =
      (Fin.cons x.val (Fin.cons y.val (fun j : Fin φ.fvSup ↦ (e j.val).val))) ∘
        Fin.cast (Nat.add_comm 2 φ.fvSup) := by
    change (fun i ↦ (Fin.append (Fin.cons x (Fin.cons y Fin.elim0))
      (fun j : Fin φ.fvSup ↦ e j.val) i).val) = _
    rw [Fin.append_cons, Fin.append_left_eq_cons]
    funext i
    simp only [Function.comp_apply]
    generalize hj : Fin.cast (Nat.add_comm 2 φ.fvSup) i = j
    have hi : i = Fin.cast (Nat.add_comm φ.fvSup 2) j := by rw [← hj]; rfl
    subst i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) j <;> simp
    rfl
  rw [ht, standardTuple_cast] at h
  simpa [Nat.add_comm 2, num_succ_def, standardTuple] using h

theorem InternalSeparation.models_schema {A : V} (hA : IsNonempty A)
    [Nonempty (SetDomain A)] (hs : InternalSeparation A) (φ : SetTheorySemiproposition 1) :
    (SetDomain A)↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  have hc : IsMembershipFormulaCode (succ (φ.fvSup : V))
      (encodeMembershipFormula (closeParameters φ)) := by
    have h := (mem_formulaSet_iff _ _ _ _).mp
      (encodeMembershipFormula_mem (V := V) (closeParameters φ))
    simpa [IsMembershipFormulaCode, Nat.add_comm 1, num_succ_def] using h
  obtain ⟨c, hcA, hc⟩ := hs (φ.fvSup : V) (by simp) _ hc _
    (standardTuple_mem_function (fun i : Fin φ.fvSup ↦ (e i.val).val) (fun i ↦ (e i.val).property))
    a.val a.property
  refine ⟨⟨c, hcA⟩, ?_⟩
  intro x
  change x.val ∈ c ↔ x.val ∈ a.val ∧ φ.Eval ![x] e
  rw [hc x.val x.property, membershipSatisfies_closeParameters_one hA φ x e]

theorem InternalReplacement.models_schema {A : V} (hA : IsNonempty A)
    [Nonempty (SetDomain A)] (hr : InternalReplacement A) (φ : SetTheorySemiproposition 2) :
    (SetDomain A)↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  let b := standardTuple (fun i : Fin φ.fvSup ↦ (e i.val).val)
  let R := fun x y ↦ MembershipSatisfies A (succ (succ (φ.fvSup : V)))
    (encodeMembershipFormula (closeParameters φ))
    (assignmentPrepend (succ (φ.fvSup : V)) (assignmentPrepend (φ.fvSup : V) b y) x)
  have hR (x y : SetDomain A) : R x.val y.val ↔ φ.Eval ![x, y] e :=
    membershipSatisfies_closeParameters_two hA φ x y e
  have hc : IsMembershipFormulaCode (succ (succ (φ.fvSup : V)))
      (encodeMembershipFormula (closeParameters φ)) := by
    have h := (mem_formulaSet_iff _ _ _ _).mp
      (encodeMembershipFormula_mem (V := V) (closeParameters φ))
    simpa [IsMembershipFormulaCode, Nat.add_comm 2, num_succ_def] using h
  have hex : ∀ x ∈ A, x ∈ a.val → ∃! y, y ∈ A ∧ R x y := by
    intro x hx _
    let u : SetDomain A := ⟨x, hx⟩
    obtain ⟨y, hy, huy⟩ := hf u
    refine ⟨y.val, ⟨y.property, (hR u y).mpr hy⟩, ?_⟩
    intro z hz
    exact congrArg Subtype.val (huy ⟨z, hz.1⟩ ((hR u ⟨z, hz.1⟩).mp hz.2))
  obtain ⟨c, hcA, hc⟩ := hr (φ.fvSup : V) (by simp) _ hc b
    (standardTuple_mem_function _ (fun i ↦ (e i.val).property)) a.val a.property hex
  refine ⟨⟨c, hcA⟩, ?_⟩
  intro y
  change y.val ∈ c ↔ ∃ x : SetDomain A, x.val ∈ a.val ∧ φ.Eval ![x, y] e
  rw [hc y.val y.property]
  constructor
  · rintro ⟨x, hx, hxa, hxy⟩
    exact ⟨⟨x, hx⟩, hxa, (hR ⟨x, hx⟩ y).mp hxy⟩
  · rintro ⟨x, hxa, hxy⟩
    exact ⟨x.val, x.property, hxa, (hR x y).mpr hxy⟩

theorem IsInternalZFModel.models_zf {A : V} [Nonempty (SetDomain A)]
    (hA : IsInternalZFModel A) : (SetDomain A)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  obtain ⟨⟨hn, he, hx, hp, hu, hpow, hi, hf⟩, hs, hr⟩ := hA
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (SetDomain A) (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set => exact (setSentenceTrue_iff_models _ A).mp he
  | axiom_of_extentionality => exact (setSentenceTrue_iff_models _ A).mp hx
  | axiom_of_pairing => exact (setSentenceTrue_iff_models _ A).mp hp
  | axiom_of_union => exact (setSentenceTrue_iff_models _ A).mp hu
  | axiom_of_power_set => exact (setSentenceTrue_iff_models _ A).mp hpow
  | axiom_of_infinity => exact (setSentenceTrue_iff_models _ A).mp hi
  | axiom_of_foundation => exact (setSentenceTrue_iff_models _ A).mp hf
  | axiom_of_separation ψ => exact hs.models_schema hn ψ
  | axiom_of_replacement ψ => exact hr.models_schema hn ψ

end ZFVP
