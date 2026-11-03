import Blotto.GeneralPaperCachedOffsetPrice

/-! The complete fresh subtree query reads/constructs its mass once,
computes the ancestor-plus-root offset once, and reuses the retained table.
All operands follow from the actual valid/path state. W stays explicit
until the global source-address capacity is joined.
-/
namespace Blotto.GeneralPaperFreshMassPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (ancestor : ℕ)
    {height : ℕ} (n : Node height) : GeneralPaperDyadicMultiply.Result × ℕ :=
  let amount := ancestor+offset n
  let stored := GeneralPaperMassReadPrice.run primitive W c.powers n
  let applied := GeneralPaperCachedOffsetPrice.run primitive W c amount stored.1
  (applied.1,stored.2+applied.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor (offset n)+64*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    (run primitive W c ancestor n).1=fresh c.powers ancestor n := by
  have hOff : ancestor+offset n≤c.controls.precision.levelBound := by
    rw [hc]
    exact path_offset _ ancestor n hPath
  have hn : Normal c.powers.format.unit (mass c.powers n) := by
    rw [hc]
    exact (valid_cache lambda k n hValid).1
  unfold run
  dsimp only
  rw [GeneralPaperMassReadPrice.data,GeneralPaperCachedOffsetPrice.data primitive W m lambda k Qv c hc _ hOff _ hn]
  rfl

theorem offset_width (m lambda k Qv : ℕ) :
    1+binaryWordWidth (GeneralPaperPowerPrecision.levelBound lambda k)≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hG : GeneralPaperPowerPrecision.levelBound lambda k≤GeneralPaperQuantileExponentRange.cap lambda k := by
    unfold GeneralPaperQuantileExponentRange.cap
    omega
  have hw := (binaryWordWidth_mono hG).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (ancestor : ℕ) {height : ℕ} (n : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    (run primitive W c ancestor n).2≤524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let stored := GeneralPaperMassReadPrice.run primitive W c.powers n
  have hData := GeneralPaperMassReadPrice.data primitive W c.powers n
  have hOff := path_offset _ ancestor n hPath
  have hExponent : ancestor+offset n≤c.controls.precision.levelBound := by rw [hc]; exact hOff
  have hn : Normal c.powers.format.unit stored.1 := by
    rw [hData,hc]
    exact (valid_cache lambda k n hValid).1
  have hRoot : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 n := by
    intro i hi
    have hp := hPath i hi
    omega
  have hMassCap : stored.1.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := by
    rw [hData,hc]
    exact GeneralPaperTreeMassRange.cached lambda k n hHeight hValid hRoot
  have hApplied := GeneralPaperCachedOffsetPrice.work primitive hMono W m lambda k Qv c hc
    (ancestor+offset n) hExponent stored.1 hn hMassCap
  have hRead := GeneralPaperMassReadPrice.work primitive hMono W c.powers n
  have hReadWidth : GeneralPaperMassReadPrice.width c.powers.format.unit c.powers.format.fractionalBits height≤H := by
    rw [hc]
    exact GeneralPaperMassReadPrice.operand_width m lambda k Qv height hHeight
  have hReadBound := hRead.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (hMono hReadWidth)) (64*W))
  have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b)
    ancestor (offset n) (GeneralPaperPowerPrecision.levelBound lambda k) (by omega) (by omega) hOff
  have hAddBound := hAdd.trans (Nat.mul_le_mul_left 2 (hMono (offset_width m lambda k Qv)))
  change (GeneralPaperCachedOffsetPrice.run primitive W c (ancestor+offset n) stored.1).2≤262144*(M+1)*(W+primitive H) at hApplied
  change stored.2≤5*primitive H+64*W at hReadBound
  change stored.2+(GeneralPaperCachedOffsetPrice.run primitive W c (ancestor+offset n) stored.1).2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor (offset n)+64*W≤
      524288*(M+1)*(W+primitive H)
  nlinarith only [hApplied,hReadBound,hAddBound,Nat.zero_le (M*(W+primitive H))]

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) (ancestor : ℕ) {height : ℕ} (n : Node height) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let stored := GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n
  let applied := GeneralPaperCachedOffsetPrice.arithmetic c (ancestor+offset n) stored.1
  (applied.1,stored.2+applied.2+66)

theorem arithmetic_data (c : GeneralPaperMaterializedPowerCache.Cache) (ancestor : ℕ) {height : ℕ} (n : Node height) :
    (arithmetic c ancestor n).1=fresh c.powers ancestor n := by
  simp only [arithmetic,GeneralPaperMassReadPrice.data,GeneralPaperCachedOffsetPrice.arithmetic_data,fresh]

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ) {height : ℕ} (n : Node height) :
    (arithmetic c ancestor n).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let stored := GeneralPaperMassReadPrice.run (fun _ => 1) 1 c.powers n
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hRead := GeneralPaperMassReadPrice.arithmetic_work c.powers n
  have hApplied := GeneralPaperCachedOffsetPrice.arithmetic_work m lambda k Qv c hc (ancestor+offset n) stored.1
  change stored.2≤69 at hRead
  change (GeneralPaperCachedOffsetPrice.arithmetic c (ancestor+offset n) stored.1).2≤524288*(M+1)^2 at hApplied
  change stored.2+(GeneralPaperCachedOffsetPrice.arithmetic c (ancestor+offset n) stored.1).2+66≤1048576*(M+1)^2
  nlinarith only [hRead,hApplied,Nat.zero_le (M*M)]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ) {height : ℕ} (n : Node height)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    (run primitive W c ancestor n).1=(arithmetic c ancestor n).1 := by
  rw [data _ _ _ _ _ _ _ hc _ n hValid hPath,arithmetic_data]

end Blotto.GeneralPaperFreshMassPrice
