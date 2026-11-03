import Blotto.GeneralPaperDyadicHalfPrice

/-! Both actual quantile child-mass branches. Uniform intervals halve
virtually; sparse branches compute a fresh child using the retained cache.
The parent ancestor-plus-offset arithmetic and every return are priced.
-/
namespace Blotto.GeneralPaperQuantileChildPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def run (right : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (ancestor : ℕ) {height : ℕ} (n : Node (height+1)) (storedMass : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  match n with
  | .uniform _ _ =>
    let half := GeneralPaperDyadicHalfPrice.run primitive W storedMass
    (⟨half.1,8⟩,half.2+32*W)
  | .branch level _ left rightNode =>
    let child := if right then rightNode else left
    let answer := GeneralPaperFreshMassPrice.run primitive W c (ancestor+level) child
    (answer.1,answer.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor level+32*W)

theorem data (right : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ) {height : ℕ}
    (n : Node (height+1)) (storedMass : Number) (hValid : Valid lambda k n)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    (run right primitive W c ancestor n storedMass).1=
      (if right then GeneralPaperQuantileDescent.rightMass c.powers ancestor n storedMass
        else GeneralPaperQuantileDescent.leftMass c.powers ancestor n storedMass) := by
  have hChildren := child_validity lambda k n hValid
  have hPaths := child_paths _ ancestor n hPath
  cases n with
  | uniform h level =>
    cases right <;> simp only [run,GeneralPaperDyadicHalfPrice.data,Bool.false_eq_true,ite_false,ite_true,
      GeneralPaperQuantileDescent.rightMass,GeneralPaperQuantileDescent.leftMass]
  | branch level cached left rightNode =>
    cases right
    · exact GeneralPaperFreshMassPrice.data primitive W m lambda k Qv c hc (ancestor+level) left hChildren.1 hPaths.1
    · exact GeneralPaperFreshMassPrice.data primitive W m lambda k Qv c hc (ancestor+level) rightNode hChildren.2 hPaths.2

theorem work (right : Bool) (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (ancestor : ℕ) {height : ℕ} (n : Node (height+1)) (storedMass : Number) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n)
    (hNormal : Normal c.powers.format.unit storedMass)
    (hRange : storedMass.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    (run right primitive W c ancestor n storedMass).2≤1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hChildren := child_validity lambda k n hValid
  have hPaths := child_paths _ ancestor n hPath
  have hOff := path_offset _ ancestor n hPath
  cases n with
  | uniform h level =>
    have hh := GeneralPaperDyadicHalfPrice.work primitive hMono W c.powers.format.unit storedMass hNormal
    have hw : GeneralPaperDyadicHalfPrice.width c.powers.format.unit storedMass≤H := by
      rw [hc]
      exact GeneralPaperDyadicHalfPrice.operand_width m lambda k Qv storedMass hRange
    have hp := hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (hMono hw)) (32*W))
    change (GeneralPaperDyadicHalfPrice.run primitive W storedMass).2+32*W≤1048576*(M+1)*(W+primitive H)
    nlinarith only [hp,Nat.zero_le (M*(W+primitive H))]
  | branch level cached left rightNode =>
    have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b)
      ancestor level (GeneralPaperPowerPrecision.levelBound lambda k) (by change ancestor+level≤_ at hOff; omega)
      (by change ancestor+level≤_ at hOff; omega) hOff
    have hAddBound := hAdd.trans (Nat.mul_le_mul_left 2 (hMono (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)))
    have hLeft := GeneralPaperFreshMassPrice.work primitive hMono W m lambda k Qv c hc (ancestor+level) left
      (by omega) hChildren.1 hPaths.1
    have hRight := GeneralPaperFreshMassPrice.work primitive hMono W m lambda k Qv c hc (ancestor+level) rightNode
      (by omega) hChildren.2 hPaths.2
    cases right
    · change (GeneralPaperFreshMassPrice.run primitive W c (ancestor+level) left).2+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor level+32*W≤1048576*(M+1)*(W+primitive H)
      nlinarith only [hLeft,hAddBound,Nat.zero_le (M*(W+primitive H))]
    · change (GeneralPaperFreshMassPrice.run primitive W c (ancestor+level) rightNode).2+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor level+32*W≤1048576*(M+1)*(W+primitive H)
      nlinarith only [hRight,hAddBound,Nat.zero_le (M*(W+primitive H))]

def arithmetic (right : Bool) (c : GeneralPaperMaterializedPowerCache.Cache) (ancestor : ℕ)
    {height : ℕ} (n : Node (height+1)) (storedMass : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  match n with
  | .uniform _ _ =>
    let half := GeneralPaperDyadicHalfPrice.run (fun _ => 1) 1 storedMass
    (⟨half.1,8⟩,half.2+32)
  | .branch level _ left rightNode =>
    let child := if right then rightNode else left
    let answer := GeneralPaperFreshMassPrice.arithmetic c (ancestor+level) child
    (answer.1,answer.2+34)

theorem arithmetic_data (right : Bool) (c : GeneralPaperMaterializedPowerCache.Cache) (ancestor : ℕ)
    {height : ℕ} (n : Node (height+1)) (storedMass : Number) :
    (arithmetic right c ancestor n storedMass).1=
      (if right then GeneralPaperQuantileDescent.rightMass c.powers ancestor n storedMass
        else GeneralPaperQuantileDescent.leftMass c.powers ancestor n storedMass) := by
  cases n with
  | uniform h level =>
    cases right <;> simp only [arithmetic,GeneralPaperDyadicHalfPrice.data,Bool.false_eq_true,ite_false,ite_true,
      GeneralPaperQuantileDescent.rightMass,GeneralPaperQuantileDescent.leftMass]
  | branch level cached left rightNode =>
    cases right <;> simp only [arithmetic,Bool.false_eq_true,ite_false,ite_true,GeneralPaperFreshMassPrice.arithmetic_data,
      GeneralPaperQuantileDescent.rightMass,GeneralPaperQuantileDescent.leftMass]

theorem arithmetic_work (right : Bool) (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ)
    {height : ℕ} (n : Node (height+1)) (storedMass : Number) :
    (arithmetic right c ancestor n storedMass).2≤2097152*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  cases n with
  | uniform h level =>
    have hh := GeneralPaperDyadicHalfPrice.arithmetic_work storedMass
    change (GeneralPaperDyadicHalfPrice.run (fun _ => 1) 1 storedMass).2+32≤2097152*(M+1)^2
    nlinarith only [hh,Nat.zero_le (M*M)]
  | branch level cached left rightNode =>
    have hLeft := GeneralPaperFreshMassPrice.arithmetic_work m lambda k Qv c hc (ancestor+level) left
    have hRight := GeneralPaperFreshMassPrice.arithmetic_work m lambda k Qv c hc (ancestor+level) rightNode
    cases right
    · change (GeneralPaperFreshMassPrice.arithmetic c (ancestor+level) left).2+34≤2097152*(M+1)^2
      nlinarith only [hLeft,Nat.zero_le (M*M)]
    · change (GeneralPaperFreshMassPrice.arithmetic c (ancestor+level) rightNode).2+34≤2097152*(M+1)^2
      nlinarith only [hRight,Nat.zero_le (M*M)]

theorem same_data (right : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (ancestor : ℕ) {height : ℕ}
    (n : Node (height+1)) (storedMass : Number) (hValid : Valid lambda k n)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n) :
    (run right primitive W c ancestor n storedMass).1=(arithmetic right c ancestor n storedMass).1 := by
  rw [data _ _ _ _ _ _ _ _ hc _ n storedMass hValid hPath,arithmetic_data]

end Blotto.GeneralPaperQuantileChildPrice
