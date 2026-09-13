import ZFVP.SetTheory.CodedCorrectness

/-! Coded Sigma correctness supplies the support closure needed by the recursive definitions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedSigmaCorrect.bounded_witness {k : ℕ} {A : V} [IsTransitive A]
    (hA : CodedSigmaCorrect k A) {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsBoundedSetFormula ψ) (b : Fin n → V) (hb : ∀ i, b i ∈ A)
    (hex : ∃ x : V, ψ.Evalb (x :> b)) : ∃ x ∈ A, ψ.Evalb (x :> b) := by
  have hθ : IsSigmaFormula (k + 1) (.exs ψ) := .exs (.bounded hψ)
  have htruth := (domainSigmaTruth_correct k hθ b).mpr hex
  have hsat := (hA (n : V) (encodeMembershipFormula (.exs ψ)) hθ.encode (standardTuple b)
    (standardTuple_mem_function b hb)).mp htruth
  have hvalid : encodeMembershipFormula ψ ∈ formulaSet (membershipLanguageCode : V) ∅ (succ (n : V)) := by
    simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) ψ
  have hb' : standardTuple b ∈ structureDomain (membershipStructureCode A) ^ (n : V) := by
    simpa using standardTuple_mem_function b hb
  obtain ⟨x, hx, hsx⟩ := (satisfies_exists membershipLanguageCode_valid (by simp) hvalid hb').mp hsat
  have hxA : x ∈ A := by simpa using hx
  let c : Fin (n + 1) → SetDomain A := (⟨x, hxA⟩ : SetDomain A) :> fun i ↦ ⟨b i, hb i⟩
  have he : standardTuple (fun i ↦ (c i).val) = assignmentPrepend (n : V) (standardTuple b) x := rfl
  have hs' : Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ ((n + 1 : ℕ) : V)
      (encodeMembershipFormula ψ) (standardTuple (fun i ↦ (c i).val)) := by
    simpa only [num_succ_def, he] using hsx
  have hval := (satisfies_boundedMembershipFormula (show IsNonempty A from ⟨⟨x, hxA⟩⟩) hψ c).mp hs'
  refine ⟨x, hxA, ?_⟩
  have heval : (fun i ↦ (c i).val) = (x :> b) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [heval] at hval
  exact hval

theorem CodedSigmaCorrect.bounded_function_closed {k n : ℕ} {A : V} [IsTransitive A]
    (hA : CodedSigmaCorrect k A) (F : (Fin n → V) → V) {ψ : SetTheorySemisentence (n + 1)}
    [Defined (fun v : Fin (n + 1) → V ↦ v 0 = F (fun i ↦ v i.succ)) ψ]
    (hψ : IsBoundedSetFormula ψ) (b : Fin n → V) (hb : ∀ i, b i ∈ A) : F b ∈ A := by
  have heval (x : V) : ψ.Evalb (x :> b) ↔ x = F b :=
    Defined.eval_iff (R := fun v : Fin (n + 1) → V ↦ v 0 = F (fun i ↦ v i.succ)) (x :> b)
  have hex : ∃ x : V, ψ.Evalb (x :> b) := ⟨F b, (heval (F b)).mpr rfl⟩
  obtain ⟨x, hx, he⟩ := hA.bounded_witness hψ b hb hex
  have heq : x = F b := (heval x).mp he
  exact heq ▸ hx

theorem CodedSigmaCorrect.support {k : ℕ} {A : V} [IsTransitive A] (hA : CodedSigmaCorrect k A) :
    IsSequenceSupport A := by
  refine {
    toIsTransitive := inferInstance
    omega_mem := ?_
    kpair_closed := ?_
    doubleton_closed := ?_
    succ_closed := ?_
    union_closed := ?_ }
  · exact hA.bounded_function_closed (fun _ : Fin 0 → V ↦ ω) boundedOmegaFormula_bounded ![] (Fin.elim0 ·)
  · intro x hx y hy
    exact hA.bounded_function_closed (fun v : Fin 2 → V ↦ ⟨v 0, v 1⟩ₖ)
      boundedKpairFormula_bounded ![x, y] (by simpa using And.intro hx hy)
  · intro x hx y hy
    exact hA.bounded_function_closed (fun v : Fin 2 → V ↦ doubleton (v 0) (v 1))
      boundedDoubletonFormula_bounded ![x, y] (by simpa using And.intro hx hy)
  · intro x hx
    exact hA.bounded_function_closed (fun v : Fin 1 → V ↦ succ (v 0))
      boundedSuccFormula_bounded ![x] (by simpa using hx)
  · intro x hx y hy
    exact hA.bounded_function_closed (fun v : Fin 2 → V ↦ v 0 ∪ v 1)
      boundedUnionFormula_bounded ![x, y] (by simpa using And.intro hx hy)

theorem correctDomain_iff_codedCorrect (k : ℕ) {A : V} [IsTransitive A] :
    CorrectDomain (k + 1) A ↔ CodedSigmaCorrect k A := by
  rw [correctDomain_iff_codedSigmaCorrect]
  exact ⟨And.right, fun h ↦ ⟨h.support, h⟩⟩

theorem correctRankStage_iff_codedCorrect (k : ℕ) (α : V) :
    IsCorrectRankStage (k + 1) α ↔ IsOrdinal α ∧ CodedSigmaCorrect k (hierarchy α) := by
  simp only [IsCorrectRankStage]
  apply and_congr_right
  intro hα
  let := hα
  let := hierarchy_transitive α
  exact correctDomain_iff_codedCorrect k

end ZFVP
