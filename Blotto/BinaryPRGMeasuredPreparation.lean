import Blotto.BinaryPRGPromiseWork
import Blotto.BinaryPRGFrame

/-! Parsed canonical original words feed one priced promise checker and,
only on acceptance, one retained native numerical preparation. Rejection and
all prepared bytes/certificates equal the original producer. The primitive
prices are derived on arbitrary decoded words; frame parsing, complete
control/copy/physical execution and storage are separate. -/

namespace Blotto.BinaryPRGMeasuredPreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition BinaryPRGPreparation

structure Ledger where
  promise : ℕ
  numerical : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.promise + ledger.numerical

def prepareChecked {n : ℕ} (input : Input n) (hC : input.Canonical) :
    Option {prepared : Prepared n // prepared.Valid} × Ledger :=
  let checked := BinaryPRGPromiseWork.checkWithWork input
  if h : checked.1 = true then
    let prepared := BinaryPRGPreparationWork.prepareWithWork input
    have hCheck : input.Checks := (checkBool_iff input hC).mp ((BinaryPRGPromiseWork.checkWithWork_state input).symm.trans h)
    have hValid : prepared.1.Valid := by rw [BinaryPRGPreparationWork.prepareWithWork_refines]; exact prepare_valid input hC hCheck
    (some ⟨prepared.1,hValid⟩,⟨checked.2,prepared.2⟩)
  else (none,⟨checked.2,0⟩)

theorem prepareChecked_state {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (prepareChecked input hC).1 = BinaryPRGPreparation.prepareChecked input hC := by
  unfold prepareChecked BinaryPRGPreparation.prepareChecked
  dsimp only
  split
  · rename_i hTrue
    have hOld := (BinaryPRGPromiseWork.checkWithWork_state input).symm.trans hTrue
    rw [dite_eq_left hOld]
    apply congrArg some
    apply Subtype.ext
    exact BinaryPRGPreparationWork.prepareWithWork_refines input
  · rename_i hFalse
    have hOld : ¬checkBool input = true := fun h => hFalse ((BinaryPRGPromiseWork.checkWithWork_state input).trans h)
    rw [dite_eq_right hOld]

def bound {n : ℕ} (input : Input n) : ℕ := BinaryPRGPromiseWork.bound input +
  (1 + 2 * n) * (12000 * (3 * BinaryPRGPreparationWork.storedInputWidth input + 2) ^ 3)

theorem prepareChecked_bound {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (prepareChecked input hC).2.recorded ≤ bound input := by
  have hp := BinaryPRGPromiseWork.checkWithWork_bound input hC
  have hn := BinaryPRGPreparationWork.prepareWithWork_bound input
  unfold prepareChecked
  dsimp only
  split <;> dsimp only [Ledger.recorded] <;> unfold bound <;> omega

theorem prepareChecked_numerical_of_reject {n : ℕ} (input : Input n) (hC : input.Canonical)
    (h : (prepareChecked input hC).1 = none) : (prepareChecked input hC).2.numerical = 0 := by
  by_cases hc : (BinaryPRGPromiseWork.checkWithWork input).1 = true
  · have hs : (prepareChecked input hC).1.isSome = true := by
      unfold prepareChecked
      rw [dite_eq_left hc]
      rfl
    rw [h] at hs
    cases hs
  · unfold prepareChecked
    rw [dite_eq_right hc]

def readChecked (bits : List Bool) : Option ((Σ n, {prepared : Prepared n // prepared.Valid}) × List Bool) × Ledger :=
  match BinaryPRGFrame.read bits with
  | none => (none,⟨0,0⟩)
  | some parsed =>
      let checked := prepareChecked parsed.1.2.input parsed.1.2.canonical
      (checked.1.map (fun result => (⟨parsed.1.1,result⟩,parsed.2)),checked.2)

theorem readChecked_state (bits : List Bool) : (readChecked bits).1 = BinaryPRGFrame.readChecked bits := by
  unfold readChecked BinaryPRGFrame.readChecked
  cases he : BinaryPRGFrame.read bits
  · rfl
  · simp only [Option.bind_some,prepareChecked_state]

theorem readChecked_bound (bits : List Bool) :
    (readChecked bits).2.recorded ≤ match BinaryPRGFrame.read bits with
      | none => 0
      | some parsed => bound parsed.1.2.input := by
  unfold readChecked
  cases he : BinaryPRGFrame.read bits
  · exact Nat.zero_le _
  · exact prepareChecked_bound _ _

end Blotto.BinaryPRGMeasuredPreparation
