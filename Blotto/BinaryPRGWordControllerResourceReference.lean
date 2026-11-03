import Blotto.BinaryPRGWordControllerCategoricalReference
import Blotto.BinaryGeneralResourceRun

/-! Proof-only complete-coin decomposition of the retained resource controller.
Completed coins resume the actual selected Certified state, at their exact
absolute returned position and under the original shared seed cap. -/

namespace Blotto.BinaryPRGWordControllerResourceReference
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice
variable {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}

def resume (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (result : Option Bool × ℕ) (hp : result.2 ≤ N) : Option (Certified capacity) × ℕ :=
  match result.1 with
  | none => (none,result.2)
  | some branch => BinaryGeneralResourceRun.runIndexed (hC := hC) N bits (.ready (choice.select branch)) result.2 hp

theorem resume_congr (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (first second : Option Bool × ℕ) (hFirst : first.2 ≤ N) (hSecond : second.2 ≤ N) (h : first = second) :
    resume N bits choice first hFirst = resume N bits choice second hSecond := by
  cases h
  rfl

theorem coin_compose {width : ℕ} (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice capacity hC) (a b : FixedBinaryWord width) (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (pos : ℕ) (hp : pos ≤ N) :
    BinaryGeneralResourceRun.runIndexed N bits (.coin choice a b hb hab) pos hp =
      resume N bits choice (BinaryStoredCoinIndexed.run N bits a b pos hp)
        (BinaryPRGWordControllerCategoricalReference.coin_position N bits a b pos hp).2 := by
  conv_lhs => unfold BinaryGeneralResourceRun.runIndexed
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  by_cases hz : a.isZero = true
  · simp only [hz,ite_true,dite_true,resume]
  · simp only [hz,Bool.false_eq_true,ite_false,dite_false]
    by_cases he : a.same b = true
    · simp only [he,ite_true,dite_true,resume]
    · simp only [he,Bool.false_eq_true,ite_false,dite_false]
      by_cases hr : pos < N
      · simp only [dite_eq_left hr]
        by_cases hd : bits ⟨pos,hr⟩ = (a.coinStep b).1
        · simp only [hd,ite_true]
          exact coin_compose N bits choice (a.coinStep b).2 b hb
            (a.coinStep_normalized b (by
              have hn : a.value ≠ b.value := fun h => he ((a.same_value b).mpr h)
              omega)).le (pos + 1) (by omega)
        · simp only [hd,ite_false,resume]
      · simp only [dite_eq_right hr,resume]
termination_by N - pos

theorem pending_compose (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (pos : ℕ) (hp : pos ≤ N) :
    BinaryGeneralResourceRun.runIndexed N bits (BinaryGeneralResourceRun.pending choice) pos hp =
      resume N bits choice (BinaryStoredCoinIndexed.sample choice.probability N bits pos hp)
        (BinaryPRGWordControllerCategoricalReference.coin_position N bits
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).1
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).2 pos hp).2 := by
  unfold BinaryGeneralResourceRun.pending BinaryStoredCoinIndexed.sample
  apply coin_compose

theorem prepared_state (state : Certified capacity) (choice : Choice capacity hC)
    (h : BinaryGeneralResourceChoice.prepare capacity hC state = .ask choice) : choice.state = state := by
  unfold BinaryGeneralResourceChoice.prepare at h
  split at h
  · cases Preparation.ask.inj h
    rfl
  · cases h

end Blotto.BinaryPRGWordControllerResourceReference
