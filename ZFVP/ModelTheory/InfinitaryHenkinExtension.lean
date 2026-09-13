import ZFVP.ModelTheory.InfinitaryHenkinStages
import Mathlib.Data.Nat.Pairing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage
variable {L : Language} [L.Eq]

/-- Diagonal scheduling waits until all constants of a sentence are available. -/
def schedule (e : (n : ℕ) → ℕ → Sentence (stage L n)) (i : ℕ) : Sentence (stage L i) :=
  (e (Nat.unpair i).1 (Nat.unpair i).2).lMap (between (Nat.unpair_left_le i))

theorem schedule_pair (e : (n : ℕ) → ℕ → Sentence (stage L n)) (n j : ℕ) :
    schedule e (Nat.pair n j) = (e n j).lMap (between (Nat.left_le_pair n j)) := by
  unfold schedule
  have hb := Nat.unpair_left_le (Nat.pair n j)
  change (e (Nat.unpair (Nat.pair n j)).1 (Nat.unpair (Nat.pair n j)).2).lMap (between hb) = _
  generalize h : Nat.unpair (Nat.pair n j) = p at hb ⊢
  have hp : p = (n, j) := h.symm.trans (Nat.unpair_pair n j)
  cases hp
  rfl

/-- A countable Henkin theory in the language with countably many new constants.
Finite consistency is the precise property retained at the union. -/
structure Extension (Γ : Set (Sentence L)) (F : (n : ℕ) → Set (Sentence (stage L n))) where
  carrier : Set (Sentence (limit L))
  countable : carrier.Countable
  includes : Formula.lMap (Language.Hom.add₁ L (Language.constant ℕ)) '' Γ ⊆ carrier
  finite_consistent : ∀ s : Finset (Sentence (limit L)), (∀ φ ∈ s, φ ∈ carrier) →
    KeislerDerivation.Consistent (s : Set (Sentence (limit L)))
  decides : ∀ n φ, φ ∈ F n → φ.lMap (intoLimit n) ∈ carrier ∨ .neg (φ.lMap (intoLimit n)) ∈ carrier
  conjunction_witness : ∀ n (f : ℕ → Sentence (stage L n)), .conj f ∈ F n →
    .conj (fun i ↦ (f i).lMap (intoLimit n)) ∈ carrier ∨ ∃ i, .neg ((f i).lMap (intoLimit n)) ∈ carrier
  existential_witness : ∀ n (f : Formula (stage L n) 1), .exs f ∈ F n →
    .neg (.exs (f.lMap (intoLimit n))) ∈ carrier ∨
      ∃ t : Semiterm (limit L) Empty 0, (f.lMap (intoLimit n)).substFirst t ∈ carrier

theorem exists_extension (Γ : Set (Sentence L)) (hc : KeislerDerivation.Consistent Γ)
    (hΓ : Γ.Countable) (F : (n : ℕ) → Set (Sentence (stage L n))) (hF : ∀ n, (F n).Countable) :
    Nonempty (Extension Γ F) := by
  classical
  have heach (n : ℕ) : ∃ e : ℕ → Sentence (stage L n), insert (.fo .verum) (F n) = Set.range e :=
    ((hF n).insert _).exists_eq_range (Set.insert_nonempty _ _)
  choose e he using heach
  have hcover (n : ℕ) (φ : Sentence (stage L n)) (hφ : φ ∈ F n) : ∃ j, e n j = φ := by
    apply Set.mem_range.mp
    rw [← he n]
    exact Set.mem_insert_of_mem _ hφ
  refine ⟨⟨carrier Γ (schedule e), carrier_countable Γ hc hΓ _, carrier_includes Γ _,
    carrier_finite_consistent Γ hc _, ?_, ?_, ?_⟩⟩
  · intro n φ hφ
    obtain ⟨j, hj⟩ := hcover n φ hφ
    have hd := carrier_decides Γ hc (schedule e) (Nat.pair n j)
    simpa only [schedule_pair, hj, formula_intoLimit_between] using hd
  · intro n f hf
    obtain ⟨j, hj⟩ := hcover n (.conj f) hf
    have hshape : schedule e (Nat.pair n j) =
        .conj (fun i ↦ (f i).lMap (between (Nat.left_le_pair n j))) := by
      rw [schedule_pair, hj]
      rfl
    have hw := carrier_conjunction_witness Γ hc (schedule e) (Nat.pair n j) _ hshape
    simpa only [formula_intoLimit_between] using hw
  · intro n f hf
    obtain ⟨j, hj⟩ := hcover n (.exs f) hf
    have hshape : schedule e (Nat.pair n j) = .exs (f.lMap (between (Nat.left_le_pair n j))) := by
      rw [schedule_pair, hj]
      rfl
    have hw := carrier_existential_witness Γ hc (schedule e) (Nat.pair n j) _ hshape
    simp only [formula_intoLimit_between] at hw
    rcases hw with hn | hp
    · exact Or.inl hn
    · exact Or.inr ⟨freshTerm (Nat.pair n j), hp⟩

end HenkinConstruction
end ZFVP.Infinitary


