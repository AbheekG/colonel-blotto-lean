import Blotto.GeneralPaperMassQueryMetadata

/-! One retained-table query and one product apply an integer offset.
Complete native number/work data are retained; query/product results are
shared and metadata arithmetic is charged. W is the caller reference word.
-/
namespace Blotto.GeneralPaperCachedOffsetPrice
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) (mass : Number) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let power := GeneralPaperCachedPowerQuery.query primitive W c exponent
  let product := GeneralPaperDyadicMultiplyPrice.run primitive W c.powers.format.unit c.powers.format.fractionalBits power.1.number mass
  (⟨product.1.number,power.1.work+product.1.work+16⟩,
    power.2+product.2+GeneralPaperPowerTableBounds.metadataCost primitive power.1.work product.1.work 16+64*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (hExponent : exponent≤c.controls.precision.levelBound) (mass : Number) (hMass : Normal c.powers.format.unit mass) :
    (run primitive W c exponent mass).1=GeneralPaperCachedMassJoin.applyOffset c.powers exponent mass := by
  let power := GeneralPaperCachedPowerQuery.query primitive W c exponent
  have hOff : exponent≤GeneralPaperPowerPrecision.levelBound lambda k := by
    have hh := hExponent
    rw [hc] at hh
    change exponent≤GeneralPaperPowerPrecision.levelBound lambda k at hh
    exact hh
  have hPowerData := GeneralPaperCachedPowerQuery.data primitive W m lambda k Qv c hc exponent
  have hu : 0<c.powers.format.unit := by rw [hc]; exact Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hp : c.powers.format.unit=2^c.powers.format.fractionalBits := by rw [hc]; exact GeneralPaperPowerPrecision.unit_power lambda k
  have hn : Normal c.powers.format.unit power.1.number := by
    rw [hPowerData,hc]
    exact (GeneralPaperPreparedPowers.query_certificate lambda k exponent hOff).2.1
  have hProductData := GeneralPaperDyadicMultiplyPrice.data primitive W c.powers.format.unit c.powers.format.fractionalBits
    hu hp power.1.number mass hn hMass
  unfold run
  dsimp only
  rw [hProductData,hPowerData]
  rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (exponent : ℕ) (hExponent : exponent≤c.controls.precision.levelBound) (mass : Number)
    (hMass : Normal c.powers.format.unit mass)
    (hMassCap : mass.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    (run primitive W c exponent mass).2≤262144*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let power := GeneralPaperCachedPowerQuery.query primitive W c exponent
  let product := GeneralPaperDyadicMultiplyPrice.run primitive W c.powers.format.unit c.powers.format.fractionalBits power.1.number mass
  have hPowerData := GeneralPaperCachedPowerQuery.data primitive W m lambda k Qv c hc exponent
  have hOff : exponent≤GeneralPaperPowerPrecision.levelBound lambda k := by
    have hh := hExponent
    rw [hc] at hh
    change exponent≤GeneralPaperPowerPrecision.levelBound lambda k at hh
    exact hh
  have hu : 0<c.powers.format.unit := by rw [hc]; exact Nat.zero_lt_of_lt (GeneralPaperPowerPrecision.unit_positive lambda k)
  have hp : c.powers.format.unit=2^c.powers.format.fractionalBits := by rw [hc]; exact GeneralPaperPowerPrecision.unit_power lambda k
  have hn : Normal c.powers.format.unit power.1.number := by
    rw [hPowerData,hc]
    exact (GeneralPaperPreparedPowers.query_certificate lambda k exponent hOff).2.1
  have hProductData := GeneralPaperDyadicMultiplyPrice.data primitive W c.powers.format.unit c.powers.format.fractionalBits
    hu hp power.1.number mass hn hMass
  have hQuery := GeneralPaperPowerQueryEnvelope.work primitive hMono W m lambda k Qv c hc exponent hExponent
  have hProduct := GeneralPaperDyadicMultiplyPrice.work primitive hMono W c.powers.format.unit c.powers.format.fractionalBits
    power.1.number mass hn hMass
  have hQueryCap : (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) exponent).number.exponent.natAbs≤
      GeneralPaperQuantileExponentRange.cap lambda k := by
    have hh := (GeneralPaperPowerQueryExponent.magnitude lambda k exponent).trans (Nat.add_le_add_right hOff _)
    unfold GeneralPaperQuantileExponentRange.cap
    omega
  have hProductWidth : GeneralPaperDyadicMultiplyPrice.width c.powers.format.unit c.powers.format.fractionalBits
      power.1.number mass≤H := by
    rw [hPowerData,hc]
    exact GeneralPaperStoredExponentEnvelope.multiply_width m lambda k Qv _ mass hQueryCap hMassCap
  have hProductBound := hProduct.trans (Nat.mul_le_mul_left 256 (Nat.add_le_add_left (hMono hProductWidth) W))
  have hMetaCap : power.1.work+product.1.work+16≤
      GeneralPaperMassQueryMetadata.cap c.powers.format.fractionalBits c.powers.format.columns := by
    rw [hProductData,hPowerData,hc]
    exact GeneralPaperMassQueryMetadata.native_bound lambda k exponent mass
  have hMetaWidth : 1+binaryWordWidth (GeneralPaperMassQueryMetadata.cap c.powers.format.fractionalBits c.powers.format.columns)≤H := by
    rw [hc]
    exact (GeneralPaperMassQueryMetadata.word_bound _ _).trans (GeneralPaperMassQueryMetadata.operand_width m lambda k Qv)
  have hMeta := GeneralPaperPowerTableBounds.metadata_work primitive hMono power.1.work product.1.work 16 _ H hMetaCap hMetaWidth
  change power.2≤131072*M*(W+primitive H) at hQuery
  change product.2≤256*(W+primitive H) at hProductBound
  change power.2+product.2+GeneralPaperPowerTableBounds.metadataCost primitive power.1.work product.1.work 16+64*W≤
    262144*(M+1)*(W+primitive H)
  nlinarith only [hQuery,hProductBound,hMeta,Nat.zero_le (M*(W+primitive H))]

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) (mass : Number) :
    GeneralPaperDyadicMultiply.Result × ℕ :=
  let power := GeneralPaperCachedPowerQuery.arithmetic c exponent
  let product := GeneralPaperDyadicMultiply.multiply c.powers.format.unit c.powers.format.fractionalBits power.1.number mass
  (⟨product.number,power.1.work+product.work+16⟩,power.2+product.work+128)

theorem arithmetic_data (c : GeneralPaperMaterializedPowerCache.Cache) (exponent : ℕ) (mass : Number) :
    (arithmetic c exponent mass).1=GeneralPaperCachedMassJoin.applyOffset c.powers exponent mass := by
  simp only [arithmetic,GeneralPaperCachedPowerQuery.arithmetic_data,GeneralPaperCachedMassJoin.applyOffset]

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ) (mass : Number) :
    (arithmetic c exponent mass).2≤524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hQuery := GeneralPaperCachedPowerQuery.arithmetic_work m lambda k Qv c hc exponent
  have hProduct := GeneralPaperDyadicMultiply.multiply_work c.powers.format.unit c.powers.format.fractionalBits
    (GeneralPaperCachedPowerQuery.arithmetic c exponent).1.number mass
  have hp : c.powers.format.fractionalBits≤128*M := by
    rw [hc]
    exact (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change (GeneralPaperCachedPowerQuery.arithmetic c exponent).2≤262144*(M+1)^2 at hQuery
  change (GeneralPaperCachedPowerQuery.arithmetic c exponent).2+
    (GeneralPaperDyadicMultiply.multiply c.powers.format.unit c.powers.format.fractionalBits
      (GeneralPaperCachedPowerQuery.arithmetic c exponent).1.number mass).work+128≤524288*(M+1)^2
  nlinarith only [hQuery,hProduct,hp,Nat.zero_le (M*M)]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (hExponent : exponent≤c.controls.precision.levelBound) (mass : Number) (hMass : Normal c.powers.format.unit mass) :
    (run primitive W c exponent mass).1=(arithmetic c exponent mass).1 := by
  rw [data _ _ _ _ _ _ _ hc exponent hExponent mass hMass,arithmetic_data]

end Blotto.GeneralPaperCachedOffsetPrice
