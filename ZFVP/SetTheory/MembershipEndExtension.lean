import ZFVP.SetTheory.BoundedFormulas
import ZFVP.SetTheory.MembershipIso

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

structure MembershipEndExtension (V W : Type*) [SetStructure V] [SetStructure W] where
  toFun : V → W
  injective : Function.Injective toFun
  mem_iff : ∀ x y, toFun x ∈ toFun y ↔ x ∈ y
  endExtension : ∀ x y, y ∈ toFun x → ∃ z ∈ x, y = toFun z

instance {V W : Type*} [SetStructure V] [SetStructure W] :
    CoeFun (MembershipEndExtension V W) (fun _ ↦ V → W) := ⟨MembershipEndExtension.toFun⟩

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem val_term (j : MembershipEndExtension V W) {n : ℕ} (b : Fin n → V)
    (t : SetTheorySemiterm Empty n) : t.val (fun i ↦ j (b i)) Empty.elim = j (t.val b Empty.elim) := by
  cases t with
  | bvar _ => rfl
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem map_cons (j : MembershipEndExtension V W) {n : ℕ} (x : V) (b : Fin n → V) :
    (fun i ↦ j ((x :> b) i)) = j x :> (fun i ↦ j (b i)) := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem bounded_elementary (j : MembershipEndExtension V W) {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ j (b i)) := by
  induction hφ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_rel, Structure.rel,
      Function.comp_def, j.val_term]
    · exact j.injective.eq_iff.symm
    · exact (j.mem_iff _ _).symm
  | nrel r ts =>
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_nrel, Structure.rel,
      Function.comp_def, j.val_term]
    · exact not_congr j.injective.eq_iff.symm
    · exact not_congr (j.mem_iff _ _).symm
  | and hφ hψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or hφ hψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | all t hφ ih =>
    rw [eval_boundedSetAll, eval_boundedSetAll]
    simp only [j.val_term]
    constructor
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
      simpa only [j.map_cons] using (ih (x :> b)).mp (h x hx)
    · intro h x hx
      apply (ih (x :> b)).mpr
      simpa only [j.map_cons] using h (j x) ((j.mem_iff _ _).mpr hx)
  | exs t hφ ih =>
    rw [eval_boundedSetExs, eval_boundedSetExs]
    simp only [j.val_term]
    constructor
    · rintro ⟨x, hx, hh⟩
      exact ⟨j x, (j.mem_iff _ _).mpr hx, by simpa only [j.map_cons] using (ih (x :> b)).mp hh⟩
    · rintro ⟨y, hy, hh⟩
      obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
      exact ⟨x, hx, (ih (x :> b)).mpr (by simpa only [j.map_cons] using hh)⟩

end MembershipEndExtension
end ZFVP
