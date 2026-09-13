import ZFVP.Syntax.NaturalLKRule

/-! Every local check in the finite LK witness format is primitive recursive. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Primrec

theorem primrec_list_mem {α : Type*} [Primcodable α] : PrimrecRel (fun (a : α) (l : List α) ↦ a ∈ l) := by
  exact ((PrimrecRel.exists_mem_list Primrec.eq).comp snd fst).of_eq (by simp)

theorem lkRuleCheck_primrec : PrimrecPred (fun p : List (Sequent ℒₛₑₜ) × Sequent ℒₛₑₜ × LKRuleWitness ↦
    LKRuleCheck p.1 p.2.1 p.2.2) := by
  let A := List (Sequent ℒₛₑₜ) × Sequent ℒₛₑₜ × LKRuleWitness
  have hS : Primrec (fun p : A ↦ p.1) := fst
  have hC : Primrec (fun p : A ↦ p.2.1) := fst.comp snd
  have hw : Primrec (fun p : A ↦ p.2.2) := snd.comp snd
  have ht := fst.comp hw
  have hr1 := snd.comp hw
  have hφ := fst.comp hr1
  have hr2 := snd.comp hr1
  have hψ := fst.comp hr2
  have hr3 := snd.comp hr2
  have hθ := fst.comp hr3
  have hr4 := snd.comp hr3
  have hk := fst.comp hr4
  have hr5 := snd.comp hr4
  have hΓ := fst.comp hr5
  have hΔ := snd.comp hr5
  have hnφ := (syntacticFormula_neg_primrec 0).comp hφ
  have h0 := Primrec.eq.comp hC (list_cons.comp hφ (list_cons.comp hnφ (const [])))
  have h1 := ((primrec_list_mem.comp (list_cons.comp hφ hΓ) hS).and
    ((primrec_list_mem.comp (list_cons.comp hnφ hΔ) hS).and
      (Primrec.eq.comp hC (list_append.comp hΓ hΔ))))
  have h2 := (primrec_list_mem.comp hΔ hS).and ((PrimrecRel.forall_mem_list primrec_list_mem).comp hΔ hC)
  have h3 := Primrec.eq.comp hC (const ([⊤] : Sequent ℒₛₑₜ))
  have h4 := (primrec_list_mem.comp (list_cons.comp hφ (list_cons.comp hψ hΓ)) hS).and
    (Primrec.eq.comp hC (list_cons.comp (proposition_or_primrec.comp hφ hψ) hΓ))
  have h5 := (primrec_list_mem.comp (list_cons.comp hφ hΓ) hS).and
    ((primrec_list_mem.comp (list_cons.comp hψ hΓ) hS).and
      (Primrec.eq.comp hC (list_cons.comp (proposition_and_primrec.comp hφ hψ) hΓ)))
  have hshift := Primrec.list_map hΓ (proposition_shift_primrec.comp snd).to₂
  have h6 := (primrec_list_mem.comp (list_cons.comp (proposition_free_primrec.comp hθ) hshift) hS).and
    (Primrec.eq.comp hC (list_cons.comp (proposition_all_primrec.comp hθ) hΓ))
  have h7 := (primrec_list_mem.comp (list_cons.comp (proposition_subst_primrec.comp hk hθ) hΓ) hS).and
    (Primrec.eq.comp hC (list_cons.comp (proposition_exs_primrec.comp hθ) hΓ))
  have h := ((Primrec.eq.comp ht (const 0)).and h0).or
    (((Primrec.eq.comp ht (const 1)).and h1).or
    (((Primrec.eq.comp ht (const 2)).and h2).or
    (((Primrec.eq.comp ht (const 3)).and h3).or
    (((Primrec.eq.comp ht (const 4)).and h4).or
    (((Primrec.eq.comp ht (const 5)).and h5).or
    (((Primrec.eq.comp ht (const 6)).and h6).or
      ((Primrec.eq.comp ht (const 7)).and h7)))))))
  refine h.of_eq ?_
  rintro ⟨S, C, tag, φ, ψ, θ, k, Γ, Δ⟩
  match tag with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | n + 8 => simp [LKRuleCheck, List.subset_def]

end ZFVP
