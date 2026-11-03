import Blotto.BinaryCategoricalRun
import Blotto.BinaryStoredCoinIndexedWork

/-! A proof-only sequential decomposition of the retained shared-cap
categorical machine. Each complete stored-word coin resumes the exact selected
head or original remaining suffix at its absolute returned position. -/

namespace Blotto.BinaryPRGWordControllerCategoricalReference
open BinaryCategoricalPreparation BinaryCategoricalRun

 theorem coin_position {width : ℕ} (N : ℕ) (bits : Fin N → Bool)
    (a b : FixedBinaryWord width) (pos : ℕ) (hp : pos ≤ N) :
    pos ≤ (BinaryStoredCoinIndexed.run N bits a b pos hp).2 ∧
      (BinaryStoredCoinIndexed.run N bits a b pos hp).2 ≤ N := by
  unfold BinaryStoredCoinIndexed.run
  dsimp only
  split_ifs with hz he hr hd
  · exact ⟨le_rfl,hp⟩
  · exact ⟨le_rfl,hp⟩
  · have ih := coin_position N bits (a.coinStep b).2 b (pos + 1) (by omega)
    omega
  · omega
  · exact ⟨le_rfl,hp⟩
termination_by N - pos

 def resume {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice α) (result : Option Bool × ℕ) (hp : result.2 ≤ N) : Option α × ℕ :=
  match result.1 with
  | none => (none,result.2)
  | some true => (some choice.head.1,result.2)
  | some false => BinaryCategoricalRun.runIndexed fallback N bits (.remaining choice.rest) result.2 hp

 theorem resume_congr {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice α) (first second : Option Bool × ℕ) (hFirst : first.2 ≤ N) (hSecond : second.2 ≤ N)
    (h : first = second) :
    resume fallback N bits choice first hFirst = resume fallback N bits choice second hSecond := by
  cases h
  rfl

 theorem coin_compose {α : Type*} {width : ℕ} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice α) (a b : FixedBinaryWord width) (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (pos : ℕ) (hp : pos ≤ N) :
    BinaryCategoricalRun.runIndexed fallback N bits (.coin choice a b hb hab) pos hp =
      resume fallback N bits choice (BinaryStoredCoinIndexed.run N bits a b pos hp)
        (coin_position N bits a b pos hp).2 := by
  conv_lhs => unfold BinaryCategoricalRun.runIndexed
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  by_cases hz : a.isZero = true
  · simp only [hz,ite_true,dite_true,resume]
  · simp only [hz,Bool.false_eq_true,ite_false,dite_false]
    by_cases he : a.same b = true
    · simp only [he,ite_true,dite_true,resume]
      conv_lhs => unfold BinaryCategoricalRun.runIndexed
    · simp only [he,Bool.false_eq_true,ite_false,dite_false]
      by_cases hr : pos < N
      · simp only [dite_eq_left hr]
        by_cases hd : bits ⟨pos,hr⟩ = (a.coinStep b).1
        · simp only [hd,ite_true]
          exact coin_compose fallback N bits choice (a.coinStep b).2 b hb
            (a.coinStep_normalized b (by
              have hn : a.value ≠ b.value := fun h => he ((a.same_value b).mpr h)
              omega)).le (pos + 1) (by omega)
        · simp only [hd,ite_false]
          by_cases hbit : bits ⟨pos,hr⟩ = true
          · simp only [hbit,ite_true,Bool.not_true,resume]
          · have hf : bits ⟨pos,hr⟩ = false := Bool.eq_false_of_not_eq_true hbit
            simp only [hf,Bool.false_eq_true,ite_false,Bool.not_false,resume]
            conv_lhs => unfold BinaryCategoricalRun.runIndexed
      · simp only [dite_eq_right hr,resume]
termination_by N - pos

 theorem pending_compose {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice α) (pos : ℕ) (hp : pos ≤ N) :
    BinaryCategoricalRun.runIndexed fallback N bits (pending choice) pos hp =
      resume fallback N bits choice (BinaryStoredCoinIndexed.sample choice.probability N bits pos hp)
        (coin_position N bits
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).1
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).2 pos hp).2 := by
  unfold pending BinaryStoredCoinIndexed.sample
  apply coin_compose

end Blotto.BinaryPRGWordControllerCategoricalReference
