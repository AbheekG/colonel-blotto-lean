import Blotto.GeneralPaperCachedPairBitPrice
import Blotto.GeneralPaperRationalBitSourcePair

/-! Complete explicit phase sum for the actual rational-input bit pair.
The streaming classifier/source controls and power/grid materialization
run once, followed by the cached two-source/selected-compiler phase.
Front/grid capacities use their constructed calibrated words; the common
source/compiler global address capacity and paper rates remain separate. -/
namespace Blotto.GeneralPaperRationalPairBitPrice
open GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def gridWord (m k Qv : ℕ) : ℕ :=
  GeneralPaperSourcePreparationControls.word m (alphabet m k).lambda k Qv

def gridProfile (model : RationalCostModel) (m k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.parameters m (alphabet m k).lambda k Qv
  (524288*(GeneralPaperSourcePreparationSizes.measure m (alphabet m k).lambda k Qv+1)+
    GeneralPaperProfitGridProfile.bound p.width p.exponent)*
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m (alphabet m k).lambda k Qv)

def preparationProfile (model : RationalCostModel) (Wf m k Qv B : ℕ) : ℕ :=
  GeneralPaperSourcePrecallPreparation.profile model Wf m k Qv B+gridProfile model m k Qv+128

theorem preparation_work (model : RationalCostModel) (Wf m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (GeneralPaperRationalSourcePairData.prepare model Wf (gridWord m k Qv) m k Qv b).2≤preparationProfile model Wf m k Qv B := by
  let front := GeneralPaperSourcePrecallPreparation.prepare model Wf m k Qv b
  have hData := GeneralPaperSourcePrecallPreparation.data model Wf m k Qv b
  have hControls : front.1.2=GeneralPaperSourcePreparationCache.specification m (alphabet m k).lambda k Qv :=
    congrArg Prod.snd hData
  have hFront := GeneralPaperSourcePrecallPreparation.work model Wf m k Qv b hb B hB
  have hGrid := GeneralPaperMaterializationFromControls.bit_work model m (alphabet m k).lambda k Qv front.1.2 hControls
  change front.2+(GeneralPaperMaterializationFromControls.bit model (gridWord m k Qv) k front.1.2).2+128≤_
  exact Nat.add_le_add_right (Nat.add_le_add hFront hGrid) _

def profile (model : RationalCostModel) (C d W m k Qv B p q : ℕ) : ℕ :=
  preparationProfile model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k Qv B+
    GeneralPaperCachedPairBitPrice.profile model C d W m k Qv p q+192*W

theorem actual_work {m : ℕ} {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (hColumnsIndex : binaryWordWidth (m+(prepare m k).K+1)≤W)
    (hRowsIndex : binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(prepare m k).K+m+1)≤W) :
    let f := (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy
    (GeneralPaperRationalBitSourcePair.run model W (GeneralPaperSourcePrecallPreparation.word m k Qv) (gridWord m k Qv)
      k Qv hQv weights hp hw b).2≤profile model C d W m k Qv B f.num f.den := by
  dsimp only
  let ready := GeneralPaperRationalSourcePairData.prepare model (GeneralPaperSourcePrecallPreparation.word m k Qv) (gridWord m k Qv) m k Qv b
  have hPrepare := preparation_work model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k Qv b hb B hB
  have hCached := GeneralPaperCachedPairBitPrice.actual_work hg W k Qv hm hQv weights hp hw (b:ℝ) (by exact_mod_cast hb) ready.1
    hW hDim hK hM hIndex hBatch hFinal hColumnsIndex hRowsIndex
  exact Nat.add_le_add_right (Nat.add_le_add hPrepare hCached) _

end Blotto.GeneralPaperRationalPairBitPrice
