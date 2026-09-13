import ZFVP.ModelTheory.RubinFiniteBlockUnion

/-! The types forbidding new members of old internally finite sets are locally
omitted by the same Rubin theory used for the inseparable-pair construction. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u v

def finiteMemberTemplate (C : Type u) : Semisentence (LSetC C) 2 :=
  .rel Language.Mem.mem ![#1, #0]

def finiteEqualityTemplate (C : Type u) : Semisentence (LSetC C) 2 :=
  .rel Language.Eq.eq ![#0, #1]

theorem eval_finiteMemberTemplate {C : Type u} {N : Type v} [SetStructure N]
    (c : C → N) (a : N) (x : Fin 1 → N) :
    Semiformula.Eval (s := setConstStructure N c) (a :> x) Empty.elim (finiteMemberTemplate C) ↔
      x 0 ∈ a := Iff.rfl

theorem eval_finiteEqualityTemplate {C : Type u} {N : Type v} [SetStructure N]
    (c : C → N) (a : N) (x : Fin 1 → N) :
    Semiformula.Eval (s := setConstStructure N c) (a :> x) Empty.elim (finiteEqualityTemplate C) ↔
      a = x 0 := Iff.rfl

variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def finiteNewMemberType (a : M) : PartialType (LSetC (M ⊕ ℕ)) 1 :=
  {σ | σ = substConst (finiteMemberTemplate (M ⊕ ℕ)) (Sum.inl a) ∨
    ∃ m ∈ a, σ = ∼substConst (finiteEqualityTemplate (M ⊕ ℕ)) (Sum.inl m)}

/-- Rubin's block criterion and internal finite induction establish local
omission; preservation of old finite sets is not assumed. -/
theorem finiteNewMemberType_locallyOmitted [Countable M]
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n))
    {a : M} (ha : IsInternallyFinite a) :
    LocallyOmits (rubinTheory δ ρ) (finiteNewMemberType a) := by
  intro θ hθ
  classical
  by_contra hcon
  have hno : ∀ σ ∈ finiteNewMemberType a,
      ¬Entailment.Consistent (insert (∃¹* (θ ⋏ ∼σ)) (rubinTheory δ ρ)) :=
    fun σ hσ h ↦ hcon ⟨σ, hσ, h⟩
  let ψm := finiteMemberTemplate (M ⊕ ℕ)
  let ψe := finiteEqualityTemplate (M ⊕ ℕ)
  obtain ⟨p, ks, hinj, hcov⟩ :=
    exists_indices (existsNotSat θ ψm ⋏ (existsSat θ ψe ⋏ existsBody θ))
  have hcovN : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsNotSat θ ψm) → ∃ i, ks i = k := by
    intro k hk
    apply hcov k
    rw [constSupport_and]
    exact List.mem_append_left _ hk
  have hcovS : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsSat θ ψe) → ∃ i, ks i = k := by
    intro k hk
    apply hcov k
    rw [constSupport_and]
    apply List.mem_append_right
    rw [constSupport_and]
    exact List.mem_append_left _ hk
  have hcovB : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsBody θ) → ∃ i, ks i = k := by
    intro k hk
    apply hcov k
    rw [constSupport_and]
    apply List.mem_append_right
    rw [constSupport_and]
    exact List.mem_append_right _ hk
  have hOutside : blockAllNot δ ρ ks (abstractFormula ks (existsNotSat θ ψm)) a := by
    have h1 := hno _ (Or.inl rfl)
    have h2 := consistent_insert_iff_blockEx_of_body hdir
      (∃¹* (θ ⋏ ∼substConst ψm (Sum.inl a))) hinj
      (abstractFormula ks (existsNotSat θ ψm) ⇜ paramSubst p a)
      (isBody_existsNotSat θ ψm ks hcovN a)
    rw [h2, not_blockEx_iff] at h1
    exact BlockAll.mono δ ρ (fun t ht hc ↦ ht ((eval_paramSubst _ a t id).mpr hc)) h1
  have hMembers : ∀ m ∈ a, blockAllNot δ ρ ks (abstractFormula ks (existsSat θ ψe)) m := by
    intro m hm
    have h1 := hno _ (Or.inr ⟨m, hm, rfl⟩)
    rw [show (∼(∼substConst ψe (Sum.inl m))) = substConst ψe (Sum.inl m) from by simp] at h1
    have h2 := consistent_insert_iff_blockEx_of_body hdir
      (∃¹* (θ ⋏ substConst ψe (Sum.inl m))) hinj
      (abstractFormula ks (existsSat θ ψe) ⇜ paramSubst p m)
      (isBody_existsSat θ ψe ks hcovS m)
    rw [h2, not_blockEx_iff] at h1
    exact BlockAll.mono δ ρ (fun t ht hc ↦ ht ((eval_paramSubst _ m t id).mpr hc)) h1
  have hAll := internallyFinite_blockAllNot δ ρ hdir ks (abstractFormula ks (existsSat θ ψe)) ha hMembers
  have hEx : BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id
      (abstractFormula ks (existsBody θ) ⇜ paramSubst p a) :=
    (consistent_insert_iff_blockEx_of_body hdir (∃¹* θ) hinj
      (abstractFormula ks (existsBody θ) ⇜ paramSubst p a)
      (isBody_existsBody θ ks hcovB a)).mp hθ
  apply blockAll_blockEx_contradiction δ ρ (BlockAll.and δ ρ hdir hOutside hAll) hEx
  rintro s ⟨hOut, hFin⟩ hBody
  obtain ⟨c, hcl, hcr⟩ := exists_assign_of_injective hinj s
  have hks : (fun i ↦ c (Sum.inr (ks i))) = s := funext hcr
  have hid : (fun m : M ↦ c (Sum.inl m)) = id := funext hcl
  have eB := eval_abstractFormula c ks ![a] (existsBody θ) hcovB
  have eN := eval_abstractFormula c ks ![a] (existsNotSat θ ψm) hcovN
  rw [hks, hid] at eB eN
  obtain ⟨x, hxθ⟩ := (eval_existsBody c θ a).mp
    (eB.mp ((eval_paramSubst _ a s id).mp hBody))
  have hxa : x 0 ∈ a := by
    by_contra hxa
    apply hOut
    apply eN.mpr
    exact (eval_existsNotSat c θ ψm a).mpr ⟨x, hxθ, hxa⟩
  have eS := eval_abstractFormula c ks ![x 0] (existsSat θ ψe) hcovS
  rw [hks, hid] at eS
  apply hFin (x 0) hxa
  apply eS.mpr
  exact (eval_existsSat c θ ψe (x 0)).mpr ⟨x, hxθ, rfl⟩

end ZFVP
