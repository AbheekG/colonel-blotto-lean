import Blotto.GeneralPaperParentCacheMetadata

/-! Parent recomputation reads one child mass and applies its retained root
offset once. No ancestor addition is inserted. Actual validity and path
bounds supply every native-data, normality and exponent-range premise.
-/
namespace Blotto.GeneralPaperNodeOffsetPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) {height : ℕ} (n : Node height) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let stored := GeneralPaperMassReadPrice.run price W c.powers n
  let applied := GeneralPaperCachedOffsetPrice.run price W c (offset n) stored.1
  (applied.1,stored.2+applied.2+32*W)

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) {height : ℕ} (n : Node height) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let stored := GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n
  let applied := GeneralPaperCachedOffsetPrice.arithmetic c (offset n) stored.1
  (applied.1,stored.2+applied.2+32)

theorem data (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) :
    (run price W c n).1=GeneralPaperCachedMassJoin.applyOffset c.powers (offset n) (mass c.powers n) := by
  have ho : offset n≤c.controls.precision.levelBound := by rw [hc]; exact valid_offset lambda k n hValid
  have hn : Normal c.powers.format.unit (GeneralPaperMassReadPrice.run price W c.powers n).1 := by
    rw [GeneralPaperMassReadPrice.data,hc]
    exact (valid_cache lambda k n hValid).1
  unfold run
  dsimp only
  rw [GeneralPaperCachedOffsetPrice.data price W m lambda k Qv c hc _ ho _ hn,GeneralPaperMassReadPrice.data]

theorem arithmetic_data (c : GeneralPaperMaterializedPowerCache.Cache) {height : ℕ} (n : Node height) :
    (arithmetic c n).1=GeneralPaperCachedMassJoin.applyOffset c.powers (offset n) (mass c.powers n) := by
  simp only [arithmetic,GeneralPaperCachedOffsetPrice.arithmetic_data,GeneralPaperMassReadPrice.data]

theorem normal (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) : Normal c.powers.format.unit (run price W c n).1.number := by
  rw [data price W m lambda k Qv c hc n hValid,hc]
  exact GeneralPaperCachedMassJoin.apply_normal lambda k (offset n) _ (valid_offset lambda k n hValid) (valid_cache lambda k n hValid).1

theorem exponent_range (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k n)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 n) :
    (run price W c n).1.number.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
  rw [data price W m lambda k Qv c hc n hValid,hc]
  simpa only [fresh,Nat.zero_add,GeneralPaperMaterializedPowerCache.specification,GeneralPaperQuantileExponentRange.cap] using GeneralPaperTreeMassRange.fresh lambda k 0 n hHeight hValid hPath

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (n : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k n)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 n) :
    (run price W c n).2≤524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have h := GeneralPaperFreshMassPrice.work price hMono W m lambda k Qv c hc 0 n hHeight hValid hPath
  change (GeneralPaperMassReadPrice.run price W c.powers n).2+
    (GeneralPaperCachedOffsetPrice.run price W c (0+offset n) (GeneralPaperMassReadPrice.run price W c.powers n).1).2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) 0 (offset n)+64*W≤_ at h
  rw [Nat.zero_add] at h
  change (GeneralPaperMassReadPrice.run price W c.powers n).2+
    (GeneralPaperCachedOffsetPrice.run price W c (offset n) (GeneralPaperMassReadPrice.run price W c.powers n).1).2+32*W≤_
  omega

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height) :
    (arithmetic c n).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  have hr := GeneralPaperMassReadPrice.arithmetic_work c.powers n
  have ha := GeneralPaperCachedOffsetPrice.arithmetic_work m lambda k Qv c hc (offset n)
    (GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n).1
  change (GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n).2+
    (GeneralPaperCachedOffsetPrice.arithmetic c (offset n) (GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n).1).2+32≤_
  nlinarith only [hr,ha,Nat.zero_le (GeneralPaperSourcePreparationSizes.measure m lambda k Qv)]

theorem arithmetic_normal (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) : Normal c.powers.format.unit (arithmetic c n).1.number := by
  rw [arithmetic_data,hc]
  exact GeneralPaperCachedMassJoin.apply_normal lambda k (offset n) _ (valid_offset lambda k n hValid) (valid_cache lambda k n hValid).1

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) : (run price W c n).1=(arithmetic c n).1 := by
  rw [data price W m lambda k Qv c hc n hValid,arithmetic_data]

end Blotto.GeneralPaperNodeOffsetPrice
