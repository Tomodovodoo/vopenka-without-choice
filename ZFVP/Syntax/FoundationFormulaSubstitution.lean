import ZFVP.Syntax.FoundationLiftSubstitution
import ZFVP.Syntax.FormulaSubstitutionValidity

/-! Agreement with Foundation rewriting for externally finite encoded formulas.
The recursion and its validity theorem still range over all internal syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ η : Type*}

theorem encodeSemiformula_rew_graph {L Γ Δ G : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V) (d : η → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : V))
    (he : ∀ x, e x ∈ Γ) (hd : ∀ x, d x ∈ Δ)
    (hstep : ∀ k ∈ (ω : V), G ‘ (succ k) = liftSubstitutionState L Δ (G ‘ k))
    {n m : ℕ} {k : V} (hk : k ∈ (ω : V))
    (hs : IsSubstitutionState L Γ Δ (G ‘ k))
    (hn : stateSource (G ‘ k) = (n : V)) (hm : stateTarget (G ‘ k) = (m : V))
    (σ : Rew Λ ξ n η m)
    (hB : ∀ i : Fin n, (stateBound (G ‘ k)) ‘ (i.val : V) = encodeSemiterm F d (σ (.bvar i)))
    (hE : ∀ x, (stateFree (G ‘ k)) ‘ (e x) = encodeSemiterm F d (σ (.fvar x)))
    (φ : Semiformula Λ ξ n) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨(n : V), encodeSemiformula F R e φ⟩ₖ, k⟩ₖ =
      encodeSemiformula F R d (Semiformula.rewAux σ φ) := by
  have hmem : ∀ {n} (ψ : Semiformula Λ ξ n), encodeSemiformula F R e ψ ∈ formulaSet L Γ (n : V) :=
    fun ψ ↦ (mem_formulaSet_iff _ _ _ _).mpr (encodeSemiformula_mem_family hL F R e hF hR he ψ)
  have ha : ∀ n a (r : Λ.Rel a) (ts : Fin a → Semiterm Λ ξ n),
      IsAtomicArguments L Γ (n : V) (relationToken (R r))
        (standardTuple (fun i ↦ encodeSemiterm F e (ts i))) := by
    intro n a r ts
    refine Or.inr ⟨R r, (hR a r).1, rfl, ?_⟩
    rw [(hR a r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem hL F e hF he (ts i))
  induction φ generalizing m k with
  | verum => exact formulaSubstitutionGraph_truth hL (by simp) hk Γ G
  | falsum => exact formulaSubstitutionGraph_falsity hL (by simp) hk Γ G
  | rel r ts =>
    rw [encodeSemiformula, formulaSubstitutionGraph_atom hL (by simp) hk (ha _ _ r ts)]
    rw [compose_standardTuple _ _ (fun i ↦ by simpa using encodeSemiterm_mem hL F e hF he (ts i))]
    simp only [Semiformula.rewAux, encodeSemiformula, Function.comp_apply,
      encodeSemiterm_rew hL F e d hF he σ hB hE]
  | nrel r ts =>
    rw [encodeSemiformula, formulaSubstitutionGraph_negAtom hL (by simp) hk (ha _ _ r ts)]
    rw [compose_standardTuple _ _ (fun i ↦ by simpa using encodeSemiterm_mem hL F e hF he (ts i))]
    simp only [Semiformula.rewAux, encodeSemiformula, Function.comp_apply,
      encodeSemiterm_rew hL F e d hF he σ hB hE]
  | and φ ψ ihφ ihψ =>
    rw [encodeSemiformula, formulaSubstitutionGraph_and hL (by simp) hk (hmem φ) (hmem ψ)]
    rw [ihφ hk hs hn hm σ hB hE, ihψ hk hs hn hm σ hB hE]
    rfl
  | or φ ψ ihφ ihψ =>
    rw [encodeSemiformula, formulaSubstitutionGraph_or hL (by simp) hk (hmem φ) (hmem ψ)]
    rw [ihφ hk hs hn hm σ hB hE, ihψ hk hs hn hm σ hB hE]
    rfl
  | @all n φ ih =>
    rw [encodeSemiformula, formulaSubstitutionGraph_all hL (by simp) hk (by simpa [num_succ_def] using hmem φ)]
    have hs' : IsSubstitutionState L Γ Δ (G ‘ (succ k)) := by
      rw [hstep k hk]; exact liftSubstitutionState_valid hL hs
    have hn' : stateSource (G ‘ (succ k)) = ((n + 1 : ℕ) : V) := by
      simp [hstep k hk, liftSubstitutionState, hn, num_succ_def]
    have hm' : stateTarget (G ‘ (succ k)) = ((m + 1 : ℕ) : V) := by
      simp [hstep k hk, liftSubstitutionState, hm, num_succ_def]
    have hB' := liftBoundReplacement_encode hL F d hF hd σ (by simpa [hn, hm] using hs.2.2.1) hB
    have hE' := liftFreeReplacement_encode hL F e d hF he hd σ (by simpa [hm] using hs.2.2.2) hE
    have hb : ∀ i, (stateBound (G ‘ (succ k))) ‘ (i.val : V) = encodeSemiterm F d (σ.q (.bvar i)) := by
      simpa [hstep k hk, liftSubstitutionState, hn, hm] using hB'
    have he' : ∀ x, (stateFree (G ‘ (succ k))) ‘ (e x) = encodeSemiterm F d (σ.q (.fvar x)) := by
      simpa [hstep k hk, liftSubstitutionState, hm] using hE'
    have hi := ih (ω_succ_closed hk) hs' hn' hm' σ.q hb he'
    simpa only [num_succ_def, Semiformula.rewAux, encodeSemiformula] using congrArg allCode hi
  | @exs n φ ih =>
    rw [encodeSemiformula, formulaSubstitutionGraph_exists hL (by simp) hk (by simpa [num_succ_def] using hmem φ)]
    have hs' : IsSubstitutionState L Γ Δ (G ‘ (succ k)) := by
      rw [hstep k hk]; exact liftSubstitutionState_valid hL hs
    have hn' : stateSource (G ‘ (succ k)) = ((n + 1 : ℕ) : V) := by
      simp [hstep k hk, liftSubstitutionState, hn, num_succ_def]
    have hm' : stateTarget (G ‘ (succ k)) = ((m + 1 : ℕ) : V) := by
      simp [hstep k hk, liftSubstitutionState, hm, num_succ_def]
    have hB' := liftBoundReplacement_encode hL F d hF hd σ (by simpa [hn, hm] using hs.2.2.1) hB
    have hE' := liftFreeReplacement_encode hL F e d hF he hd σ (by simpa [hm] using hs.2.2.2) hE
    have hb : ∀ i, (stateBound (G ‘ (succ k))) ‘ (i.val : V) = encodeSemiterm F d (σ.q (.bvar i)) := by
      simpa [hstep k hk, liftSubstitutionState, hn, hm] using hB'
    have he' : ∀ x, (stateFree (G ‘ (succ k))) ‘ (e x) = encodeSemiterm F d (σ.q (.fvar x)) := by
      simpa [hstep k hk, liftSubstitutionState, hm] using hE'
    have hi := ih (ω_succ_closed hk) hs' hn' hm' σ.q hb he'
    simpa only [num_succ_def, Semiformula.rewAux, encodeSemiformula] using congrArg existsCode hi

theorem encodeSemiformula_rew {L Γ Δ B E : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V) (d : η → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : V))
    (he : ∀ x, e x ∈ Γ) (hd : ∀ x, d x ∈ Δ)
    {n m : ℕ} (σ : Rew Λ ξ n η m)
    (hBmem : B ∈ termSet L Δ (m : V) ^ (n : V)) (hEmem : E ∈ termSet L Δ (m : V) ^ Γ)
    (hB : ∀ i : Fin n, B ‘ (i.val : V) = encodeSemiterm F d (σ (.bvar i)))
    (hE : ∀ x, E ‘ (e x) = encodeSemiterm F d (σ (.fvar x)))
    (φ : Semiformula Λ ξ n) :
    substituteFormula L Γ Δ (substitutionState (n : V) (m : V) B E) (encodeSemiformula F R e φ) =
      encodeSemiformula F R d (Semiformula.rew σ φ) := by
  have hs : IsSubstitutionState L Γ Δ (substitutionState (n : V) (m : V) B E) := by
    simp only [IsSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code]
    exact ⟨by simp, by simp, hBmem, hEmem⟩
  have h := encodeSemiformula_rew_graph (G := substitutionStates L Δ (substitutionState (n : V) (m : V) B E))
    hL F R e d hF hR he hd (fun k hk ↦ substitutionStates_succ L Δ _ hk)
    (k := (0 : V)) (by simp) (by simpa [substitutionStates_zero] using hs)
    (by simp [substitutionStates_zero]) (by simp [substitutionStates_zero]) σ
    (by simpa [substitutionStates_zero] using hB) (by simpa [substitutionStates_zero] using hE) φ
  have heq : (Semiformula.rew σ) φ = Semiformula.rewAux σ φ := rfl
  rw [heq]
  simpa only [substituteFormula, stateSource_code] using h

end ZFVP
