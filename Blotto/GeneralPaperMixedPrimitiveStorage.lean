import Blotto.GeneralPaperMixedBinaryAccuracyStorage

/-! Scalar and stored-word primitives with actual charge A and physical
reference S. Cached prices are the actual A-priced values. -/
namespace Blotto.GeneralPaperMixedPrimitiveStorage
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperNaturalScalarStep (word)
open GeneralPaperEqualAddressConstruction (price)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem fields_mono (S : ℕ) (xs ys : List ℕ) (h : List.Forall₂ (fun x y => x ≤ y) xs ys) :
    fields S xs ≤ fields S ys := by
  induction h with
  | nil => exact le_rfl
  | cons hxy hrest ih =>
    have hb := Nat.add_le_add_left (binaryWordWidth_mono hxy) 1
    change natBits _ ≤ natBits _ at hb
    simp only [fields, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
    omega

def scalarFoot (model : RationalCostModel) (S A a b out : ℕ) : ℕ :=
  let F := price model A a b out
  word a + word b + word out + F + fields S [F, 16 * A, 16] + 64 * S

theorem price_mono (model : RationalCostModel) (S A a b out : ℕ) (h : A ≤ S) :
    price model A a b out ≤ price model S a b out := by unfold price; omega

theorem scalar_bound (model : RationalCostModel) (S A a b out : ℕ) (h : A ≤ S) :
    scalarFoot model S A a b out ≤ 32 * price model S a b out := by
  let F := price model S a b out
  have hm := price_mono model S A a b out h
  have hw : word a + word b + word out + 16 * S + 16 ≤ F := by dsimp only [F, price]; omega
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap S F [price model A a b out, 16 * A, 16] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    dsimp only [F] at *
    rcases hz with rfl | rfl | rfl <;> omega)
  have hb := GeneralPaperNaturalScalarLifetime.counter_word F
  change fields S _ ≤ 3 * (natBits F + S) + 32 * S at hf
  dsimp only [scalarFoot]
  change _ ≤ 32 * F
  change price model A a b out ≤ F at hm
  omega

def wordFoot (S A n : ℕ) : ℕ :=
  let actual := GeneralPaperStoredWordLength.run A n
  natBits n + natBits actual.1 + actual.2 + fields S [actual.1, actual.2] + 128 * S

theorem word_price_mono (S A n : ℕ) (h : A ≤ S) :
    (GeneralPaperStoredWordLength.run A n).2 ≤ (GeneralPaperStoredWordLength.run S n).2 := by
  dsimp only [GeneralPaperStoredWordLength.run]
  omega

theorem word_bound (S A n : ℕ) (h : A ≤ S) :
    wordFoot S A n ≤ 32 * (GeneralPaperStoredWordLength.run S n).2 := by
  let F := (GeneralPaperStoredWordLength.run S n).2
  have hF : F = 32 * (binaryWordWidth n + binaryWordWidth (binaryWordWidth n) + S + 1) := rfl
  have hm : (GeneralPaperStoredWordLength.run A n).2 ≤ F := word_price_mono S A n h
  have hInput : natBits n ≤ F := by unfold natBits; omega
  have hLength : natBits (GeneralPaperStoredWordLength.run A n).1 ≤ F := by
    change 1 + binaryWordWidth (binaryWordWidth n) ≤ F
    omega
  have hf := GeneralPaperEncodedScalarStorage.fields_bound S (F + 2)
    [(GeneralPaperStoredWordLength.run A n).1, (GeneralPaperStoredWordLength.run A n).2] (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · omega
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega))
  change fields S _ ≤ 2 * (F + 2 + S) + 32 * S at hf
  dsimp only [wordFoot]
  change natBits n + natBits (GeneralPaperStoredWordLength.run A n).1 +
    (GeneralPaperStoredWordLength.run A n).2 + fields S _ + 128 * S ≤ 32 * F
  omega

theorem scalar_diagonal (model : RationalCostModel) (S a b out : ℕ) :
    scalarFoot model S S a b out = GeneralPaperAddressConstructionLifetime.scalarFoot model S a b out := rfl

theorem word_diagonal (S n : ℕ) : wordFoot S S n = GeneralPaperWordLengthLifetime.footprint S n := rfl

theorem scalar_le_diagonal (model : RationalCostModel) (S A a b out : ℕ) (h : A ≤ S) :
    scalarFoot model S A a b out ≤ scalarFoot model S S a b out := by
  have hp := price_mono model S A a b out h
  have hc := fields_mono S [price model A a b out, 16 * A, 16] [price model S a b out, 16 * S, 16]
    (.cons hp (.cons (Nat.mul_le_mul_left 16 h) (.cons le_rfl .nil)))
  dsimp only [scalarFoot]
  omega

theorem word_le_diagonal (S A n : ℕ) (h : A ≤ S) : wordFoot S A n ≤ wordFoot S S n := by
  have hp := word_price_mono S A n h
  have hc := fields_mono S
    [(GeneralPaperStoredWordLength.run A n).1, (GeneralPaperStoredWordLength.run A n).2]
    [(GeneralPaperStoredWordLength.run S n).1, (GeneralPaperStoredWordLength.run S n).2]
    (.cons le_rfl (.cons hp .nil))
  simp only [wordFoot, GeneralPaperStoredWordLength.data] at hc ⊢
  omega

end Blotto.GeneralPaperMixedPrimitiveStorage
