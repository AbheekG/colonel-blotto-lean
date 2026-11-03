import Blotto.GeneralPaperNodeOffsetPrice

/-! Complete fresh parent recomputation from the two retained children.
The same two offset products and one rounded sum supply the native number
and work annotation. All three native counter additions are priced; no old
parent mass is read and no child or query is replayed for calibration.
-/
namespace Blotto.GeneralPaperParentCachePrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) {height : ℕ} (left right : Node height) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let l := GeneralPaperNodeOffsetPrice.run price W c left
  let r := GeneralPaperNodeOffsetPrice.run price W c right
  let sum := GeneralPaperQuantileAdditionPrice.run price W c l.1.number r.1.number
  (⟨sum.1.number,l.1.work+r.1.work+sum.1.work+24⟩,
    l.2+r.2+sum.2+GeneralPaperParentCacheMetadata.cost price l.1.work r.1.work sum.1.work+128*W)

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) {height : ℕ} (left right : Node height) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let l := GeneralPaperNodeOffsetPrice.arithmetic c left
  let r := GeneralPaperNodeOffsetPrice.arithmetic c right
  let sum := GeneralPaperQuantileAdditionPrice.arithmetic c l.1.number r.1.number
  (⟨sum.1.number,l.1.work+r.1.work+sum.1.work+24⟩,
    l.2+r.2+sum.2+GeneralPaperParentCacheMetadata.cost (fun _ => 1) l.1.work r.1.work sum.1.work+128)

theorem data (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    (run price W c left right).1=GeneralPaperCachedMassJoin.recompute c.powers
      (offset left) (mass c.powers left) (offset right) (mass c.powers right) := by
  have hl := GeneralPaperNodeOffsetPrice.normal price W m lambda k Qv c hc left hLeft
  have hr := GeneralPaperNodeOffsetPrice.normal price W m lambda k Qv c hc right hRight
  have hs := GeneralPaperQuantileAdditionPrice.data price W m lambda k Qv c hc
    (GeneralPaperNodeOffsetPrice.run price W c left).1.number (GeneralPaperNodeOffsetPrice.run price W c right).1.number hl hr
  unfold run
  dsimp only
  rw [hs,GeneralPaperNodeOffsetPrice.data price W m lambda k Qv c hc left hLeft,
    GeneralPaperNodeOffsetPrice.data price W m lambda k Qv c hc right hRight]
  rfl

theorem arithmetic_data (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    (arithmetic c left right).1=GeneralPaperCachedMassJoin.recompute c.powers
      (offset left) (mass c.powers left) (offset right) (mass c.powers right) := by
  have hl := GeneralPaperNodeOffsetPrice.arithmetic_normal m lambda k Qv c hc left hLeft
  have hr := GeneralPaperNodeOffsetPrice.arithmetic_normal m lambda k Qv c hc right hRight
  have hs := GeneralPaperQuantileAdditionPrice.arithmetic_data m lambda k Qv c hc
    (GeneralPaperNodeOffsetPrice.arithmetic c left).1.number (GeneralPaperNodeOffsetPrice.arithmetic c right).1.number hl hr
  unfold arithmetic
  dsimp only
  rw [hs,GeneralPaperNodeOffsetPrice.arithmetic_data,GeneralPaperNodeOffsetPrice.arithmetic_data]
  rfl

theorem annotation (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    (run price W c left right).1.work≤GeneralPaperParentCacheMetadata.cap c.powers.format.fractionalBits c.powers.format.columns := by
  rw [data price W m lambda k Qv c hc left right hLeft hRight,hc]
  exact GeneralPaperParentCacheMetadata.native_bound lambda k _ _ _ _

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (left right : Node height) (hHeight : height≤lambda+1)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right)
    (hLeftPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 left)
    (hRightPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 right) :
    (run price W c left right).2≤2097152*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let l := GeneralPaperNodeOffsetPrice.run price W c left
  let r := GeneralPaperNodeOffsetPrice.run price W c right
  let sum := GeneralPaperQuantileAdditionPrice.run price W c l.1.number r.1.number
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hl := GeneralPaperNodeOffsetPrice.work price hMono W m lambda k Qv c hc left hHeight hLeft hLeftPath
  have hr := GeneralPaperNodeOffsetPrice.work price hMono W m lambda k Qv c hc right hHeight hRight hRightPath
  have hs := GeneralPaperQuantileAdditionPrice.work price hMono W m lambda k Qv c hc l.1.number r.1.number
    (GeneralPaperNodeOffsetPrice.normal price W m lambda k Qv c hc left hLeft)
    (GeneralPaperNodeOffsetPrice.normal price W m lambda k Qv c hc right hRight)
    (GeneralPaperNodeOffsetPrice.exponent_range price W m lambda k Qv c hc left hHeight hLeft hLeftPath)
    (GeneralPaperNodeOffsetPrice.exponent_range price W m lambda k Qv c hc right hHeight hRight hRightPath)
  have hCap := annotation price W m lambda k Qv c hc left right hLeft hRight
  change l.1.work+r.1.work+sum.1.work+24≤GeneralPaperParentCacheMetadata.cap c.powers.format.fractionalBits c.powers.format.columns at hCap
  have hw : 1+binaryWordWidth (GeneralPaperParentCacheMetadata.cap c.powers.format.fractionalBits c.powers.format.columns)≤H := by
    rw [hc]
    exact GeneralPaperParentCacheMetadata.operand_width m lambda k Qv
  have hm := GeneralPaperParentCacheMetadata.work price hMono l.1.work r.1.work sum.1.work _ H hCap hw
  change l.2+r.2+sum.2+GeneralPaperParentCacheMetadata.cost price l.1.work r.1.work sum.1.work+128*W≤2097152*(M+1)*(W+price H)
  nlinarith only [hl,hr,hs,hm,Nat.zero_le (M*(W+price H))]

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height) :
    (arithmetic c left right).2≤4194304*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let l := GeneralPaperNodeOffsetPrice.arithmetic c left
  let r := GeneralPaperNodeOffsetPrice.arithmetic c right
  let sum := GeneralPaperQuantileAdditionPrice.arithmetic c l.1.number r.1.number
  have hl := GeneralPaperNodeOffsetPrice.arithmetic_work m lambda k Qv c hc left
  have hr := GeneralPaperNodeOffsetPrice.arithmetic_work m lambda k Qv c hc right
  have hs := GeneralPaperQuantileAdditionPrice.arithmetic_work m lambda k Qv c hc l.1.number r.1.number
  rw [show (arithmetic c left right).2=l.2+r.2+sum.2+GeneralPaperParentCacheMetadata.cost (fun _ => 1) l.1.work r.1.work sum.1.work+128 from rfl,
    GeneralPaperParentCacheMetadata.arithmetic_cost]
  nlinarith only [hl,hr,hs,Nat.zero_le (GeneralPaperSourcePreparationSizes.measure m lambda k Qv)]

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    (run price W c left right).1=(arithmetic c left right).1 := by
  rw [data price W m lambda k Qv c hc left right hLeft hRight,arithmetic_data m lambda k Qv c hc left right hLeft hRight]

theorem normal (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    Normal c.powers.format.unit (run price W c left right).1.number := by
  rw [data price W m lambda k Qv c hc left right hLeft hRight,hc]
  exact GeneralPaperCachedMassJoin.recompute_normal lambda k (offset left) (offset right) _ _
    (valid_offset lambda k left hLeft) (valid_offset lambda k right hRight)
    (valid_cache lambda k left hLeft).1 (valid_cache lambda k right hRight).1

theorem rebuilt_valid (price : ℕ → ℕ) (W m lambda k Qv level : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLevel : level≤GeneralPaperPowerPrecision.levelBound lambda k) (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    Valid lambda k (.branch level (run price W c left right).1.number left right) := by
  rw [data price W m lambda k Qv c hc left right hLeft hRight,hc]
  exact GeneralPaperIntervalCache.rebuild_valid lambda k level left right hLevel hLeft hRight

theorem arithmetic_rebuilt_valid (m lambda k Qv level : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (left right : Node height)
    (hLevel : level≤GeneralPaperPowerPrecision.levelBound lambda k) (hLeft : Valid lambda k left) (hRight : Valid lambda k right) :
    Valid lambda k (.branch level (arithmetic c left right).1.number left right) := by
  rw [arithmetic_data m lambda k Qv c hc left right hLeft hRight,hc]
  exact GeneralPaperIntervalCache.rebuild_valid lambda k level left right hLevel hLeft hRight

end Blotto.GeneralPaperParentCachePrice
