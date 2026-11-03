import Blotto.GeneralPaperRetainedTransferPrice
import Blotto.GeneralPaperInitializerGridPrice
import Blotto.GeneralPaperInitializerControlBits

/-! Construct initializer controls and its stored integer grid once, and
retain the already-built strict-score matrix for the basis/rechecks.
H and proxy integers are retained numeric controls, not reconstructed input
encodings. The canonical Shared inputs are erased equality observers. -/
namespace Blotto.GeneralPaperRetainedBasisInputs
set_option autoImplicit false
set_option maxHeartbeats 2800000

def controls (bits : Bool) (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) :
    (GeneralPaperInitializerParameters.Parameters×ℤ)×ℕ :=
  if bits then GeneralPaperInitializerControlBits.run model W m H p q reciprocal
    else GeneralPaperInitializerControlWork.run m H p q reciprocal

theorem controls_data (bits : Bool) (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) :
    (controls bits model W m H p q reciprocal).1=
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal,GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) := by
  cases bits with
  | false => exact GeneralPaperInitializerControlWork.data m H p q reciprocal
  | true =>
    exact (GeneralPaperInitializerControlBits.data model W m H p q reciprocal).trans
      (GeneralPaperInitializerControlWork.data m H p q reciprocal)

def grid {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W N depth : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m K) :
    (GeneralPaperDictionary.Dictionary T m K×GeneralPaperBasisStoredProducts.Vector (m*(K-1)))×ℕ :=
  if bits then GeneralPaperInitializerGridPrice.run model W N depth d else GeneralPaperInitializerGridPrice.unit N depth d

theorem grid_data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W N depth : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m K) (hN : 0<N) :
    (grid bits model W N depth d).1=(GeneralPaperInitializerDictionary.build d N depth,
      GeneralPaperBasisGridInputs.grid N (GeneralPaperInitializerGridPrice.nativePoint d N depth)) := by
  cases bits with
  | false =>
    exact (GeneralPaperInitializerGridPrice.data_unit model W N depth d).symm.trans
      (GeneralPaperInitializerGridPrice.data model W N depth d hN)
  | true => exact GeneralPaperInitializerGridPrice.data model W N depth d hN

def run {T m K S : ℕ} (bits : Bool) (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) :
    GeneralPaperSharedBasisInputs.Inputs T m K×ℕ :=
  let selected := controls bits model W m H p q reciprocal
  let initial := grid bits model W selected.1.1.N selected.1.1.depth prep.dictionary
  (⟨selected.1.1,selected.1.2,initial.1.2,matrix⟩,selected.2+initial.2+64*W)

theorem data {T m K S : ℕ} (bits : Bool) (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    (run bits model W H p q reciprocal prep matrix).1=
      (⟨GeneralPaperInitializerParameters.prepare m H p q reciprocal,
        GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal,
        GeneralPaperBasisGridInputs.grid (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N
          (GeneralPaperInitializerGridPrice.nativePoint prep.dictionary
            (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N (GeneralPaperInitializerParameters.prepare m H p q reciprocal).depth),
        matrix⟩ : GeneralPaperSharedBasisInputs.Inputs T m K) := by
  dsimp only [run]
  rw [controls_data,grid_data bits model W _ _ prep.dictionary (GeneralPaperInitializerParameters.N_positive m H p q reciprocal hm hH hp hq)]

theorem actual_data {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W k p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S)
    (v : RationalFieldSelector m) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field (GeneralPaperProxyParameters.prepare m k).K))
    (hMatrix : matrix=(GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (GeneralPaperProxyParameters.prepare m k).S).1)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (run bits model W (GeneralPaperProxyParameters.prepare m k).H p q reciprocal prep matrix).1=
      GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal := by
  rw [data bits model W _ p q reciprocal prep matrix hm (GeneralPaperProxyParameters.H_positive m k) hp hq,hMatrix]
  rfl

end Blotto.GeneralPaperRetainedBasisInputs
