import Blotto.GeneralPaperRangeGeometryPrice
import Blotto.GeneralPaperRangeRootPrice

/-! Native visit/work bounds derive the complete traversal's counter word.
The five native additions at a partial node are priced without a trace,
length, work-sum, encoding or child-replay pass. Covered output levels also
derive the actual root-increment operands.
-/
namespace Blotto.GeneralPaperRangeCounterPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperRangeUpdateExecution GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def cap (lambda k : ℕ) : ℕ :=
  let f := GeneralPaperPowerPrecision.prepare lambda k
  (4*(lambda+1)+2)*(GeneralPaperParentCacheMetadata.cap f.fractionalBits f.columns+64)

theorem node_work (lambda k : ℕ) : GeneralPaperIntervalUpdateWork.nodeWork (GeneralPaperPreparedPowers.prepare lambda k)≤
    GeneralPaperParentCacheMetadata.cap (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
      (GeneralPaperPowerPrecision.prepare lambda k).columns := by
  change _≤GeneralPaperParentCacheMetadata.cap (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits
    (GeneralPaperPreparedPowers.prepare lambda k).format.columns
  unfold GeneralPaperIntervalUpdateWork.nodeWork GeneralPaperParentCacheMetadata.cap
  nlinarith only [Nat.zero_le ((GeneralPaperPreparedPowers.prepare lambda k).format.columns*
    (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits)]

theorem operand_width (m lambda k Qv : ℕ) : 1+binaryWordWidth (cap lambda k)≤
    GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let p := (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
  let columns := (GeneralPaperPowerPrecision.prepare lambda k).columns
  have hP := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hC := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hLambda : binaryWordWidth (lambda+1)≤M := by dsimp [M,GeneralPaperSourcePreparationSizes.measure]; omega
  have hParent := GeneralPaperParentCacheMetadata.word_bound p columns
  have hA := binaryWordWidth_mul 4 (lambda+1)
  have hB := GeneralPaperRayOperandWidthEnvelope.word_add (4*(lambda+1)) 2
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperParentCacheMetadata.cap p columns) 64
  have hProduct := binaryWordWidth_mul (4*(lambda+1)+2) (GeneralPaperParentCacheMetadata.cap p columns+64)
  have h4 : binaryWordWidth 4=3 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  change p≤128*M at hP
  change columns≤32*M at hC
  change 128≤M at hM
  change 1+binaryWordWidth ((4*(lambda+1)+2)*(GeneralPaperParentCacheMetadata.cap p columns+64))≤1048576*M
  omega

theorem native_bounds (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ)
    (hHeight : height≤lambda+1) (hSpan : 0<span) :
    let found := GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k) lo hi amount height n start span
    found.work≤cap lambda k ∧ found.visits≤cap lambda k := by
  let P := GeneralPaperParentCacheMetadata.cap (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
    (GeneralPaperPowerPrecision.prepare lambda k).columns
  have hv := GeneralPaperIntervalUpdate.visits_linear (GeneralPaperPreparedPowers.prepare lambda k) lo hi amount height n start span hSpan
  have hw := GeneralPaperIntervalUpdateWork.run_work lambda k lo hi amount height n start span
  have hV : (GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k) lo hi amount height n start span).visits≤4*(lambda+1)+1 := by omega
  have hWork := hw.trans (Nat.mul_le_mul hV (node_work lambda k))
  change _≤(4*(lambda+1)+1)*P at hWork
  constructor <;> unfold cap <;> dsimp only
  · nlinarith only [hWork,Nat.zero_le P]
  · nlinarith only [hV,Nat.zero_le P]

theorem metadata_work {height : ℕ} (price : ℕ → ℕ) (hMono : Monotone price)
    (left right : GeneralPaperIntervalUpdate.Result height) (joined : GeneralPaperDyadicMultiply.Result) (C H : ℕ)
    (hWork : left.work+right.work+joined.work+48≤C) (hVisits : 1+left.visits+right.visits≤C)
    (hWidth : 1+binaryWordWidth C≤H) : metadataCost price left right joined≤10*price H := by
  have hA := GeneralPaperPowerTableBounds.metadata_work price hMono left.work right.work joined.work C H (by omega) hWidth
  have hB := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun x y => x+y)
    (left.work+right.work+joined.work) 48 C (by omega) (by omega) hWork).trans (Nat.mul_le_mul_left 2 (hMono hWidth))
  have hC := GeneralPaperPowerTableBounds.metadata_work price hMono 1 left.visits right.visits C H hVisits hWidth
  unfold metadataCost GeneralPaperPowerTableBounds.metadataCost at *
  omega

theorem covered_root_bound (prepared : GeneralPaperPreparedPowers.Prepared) (lambda k : ℕ)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ)
    (hD : ¬Disjoint start span lo hi) (hC : Covered start span lo hi)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run prepared lo hi amount height n start span).node) :
    offset n+amount≤GeneralPaperPowerPrecision.levelBound lambda k := by
  have h := hOutput 0 (Nat.two_pow_pos height)
  rw [GeneralPaperIntervalUpdate.run.eq_def,ite_eq_right hD,ite_eq_left hC] at h
  change 0+levelAt (raiseRoot amount n) 0≤GeneralPaperPowerPrecision.levelBound lambda k at h
  rw [raised_level] at h
  have ho := offset_le_level n 0
  omega

theorem raise_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv amount : ℕ) {height : ℕ} (n : Node height)
    (hBound : offset n+amount≤GeneralPaperPowerPrecision.levelBound lambda k) :
    raiseCost price W amount n≤2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W := by
  have h := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun x y => x+y) (offset n) amount
    (GeneralPaperPowerPrecision.levelBound lambda k) (by omega) (by omega) hBound).trans
      (Nat.mul_le_mul_left 2 (hMono (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)))
  exact Nat.add_le_add_right h _

end Blotto.GeneralPaperRangeCounterPrice
