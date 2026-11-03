import Blotto.BinaryRulerPrecisionWork
import Blotto.BinaryArrayProjectionLifetime

/-! The legacy input-value projection and both ruler loops have a measured
data path. The reached raw reader now supplies its retained parser row list
directly; the supplied-row counterpart below measures that selected path.
Other native get/reference-bit and scalar prices remain separate obligations. -/
namespace Blotto.BinaryPRGRequestRulersWork
open RationalLottoResourceSystem

def rulersWithWork {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) : (List Bool × List Bool) × ℕ :=
  let rows := BinaryArrayProjectionLifetime.readWithWork checked.val.original.values.data
  let rulers := BinaryRulerPrecisionWork.rulersWithWork rows.1 accuracy
  (rulers.1,rows.2+rulers.2+4)

theorem rulers_state {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) :
    (rulersWithWork checked accuracy).1 =
      ((BinaryPRGRequestRulers.assembleWithTrace checked accuracy header).1.precisionRuler,
        (BinaryPRGRequestRulers.assembleWithTrace checked accuracy header).1.choiceRuler) := by
  simp only [rulersWithWork,BinaryArrayProjectionLifetime.read_work_state,
    BinaryRulerPrecisionWork.rulers_state,BinaryPRGRequestRulers.assembleWithTrace]

theorem rulers_work {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (rulersWithWork checked accuracy).2 ≤
      1024*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  have hr := BinaryArrayProjectionLifetime.read_work checked.val.original.values.data
  have hRulers := BinaryRulerPrecisionWork.rulers_work
    (BinaryArrayProjectionLifetime.readWithWork checked.val.original.values.data).1 accuracy
  have hRows : (BinaryArrayProjectionLifetime.readWithWork checked.val.original.values.data).1.length = n := by
    rw [BinaryArrayProjectionLifetime.read_work_state,BinaryArrayProjectionLifetime.read_state,
      Array.length_toList,checked.val.original.values.size]
  rw [checked.val.original.values.size] at hr
  rw [hRows] at hRulers
  unfold rulersWithWork
  dsimp only
  omega

def rulersWithRowsWork (rows : List BinaryRationalNormalization.SignedWord)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) : (List Bool × List Bool) × ℕ :=
  BinaryRulerPrecisionWork.rulersWithWork rows accuracy

theorem rulersWithRows_state {n : ℕ}
    (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (rulersWithRowsWork rows accuracy).1 =
      ((BinaryPRGRequestRulers.assembleWithRows checked accuracy header rows hRows).1.precisionRuler,
        (BinaryPRGRequestRulers.assembleWithRows checked accuracy header rows hRows).1.choiceRuler) := by
  exact BinaryRulerPrecisionWork.rulers_state rows accuracy

theorem rulersWithRows_work {n : ℕ}
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (rulersWithRowsWork rows accuracy).2 ≤
      512*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+8) := by
  simpa only [rulersWithRowsWork,hRows] using BinaryRulerPrecisionWork.rulers_work rows accuracy

end Blotto.BinaryPRGRequestRulersWork
