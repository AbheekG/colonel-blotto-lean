import Blotto.GeneralPaperQuantileSearchControls

/-! Complete root-search prices join the actual fresh/descent/path results.
The code word has one bit per level; the floating/control word is derived
separately. The original normalized CDF bracket is unchanged in both models.
-/
namespace Blotto.GeneralPaperQuantileSearchPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileSearchExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W m lambda k Qv height : ℕ) : ℕ :=
  16777216*(height+1)*(measure m lambda k Qv+1)*
    (W+primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))+
  128*(height+1)*(W+primitive (8+2*(height+1)))

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run true primitive W c digits j height node).2≤profile primitive W m lambda k Qv height := by
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let B := W+primitive (4*H)
  let t := total true primitive W c node
  let d := GeneralPaperQuantileDescentExecution.run true primitive W c digits j t.1.number height node 0 t.1.number zero
  have ht := total_data true primitive W m lambda k Qv c hc node hValid hPath
  have hm : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) (trueMass k 0 node) t.1.number := by
    rw [ht,hc]; exact fresh_bound lambda k 0 node hHeight hValid hPath
  have hz := (zero_bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)).1
  have hSafe : GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
      t.1.number height node 0 t.1.number zero := by
    rw [ht,hc]
    exact GeneralPaperQuantileExponentRange.initial lambda k digits j _ height node hHeight hValid hPath
  have hd := GeneralPaperQuantileDescentData.data true primitive W m lambda k Qv digits j c hc t.1.number height node 0 t.1.number zero
    hHeight hValid hPath hm hz
  have hF := GeneralPaperFreshMassPrice.work primitive hMono W m lambda k Qv c hc 0 node hHeight hValid hPath
  have hD := GeneralPaperQuantileDescentBits.work primitive hMono W m lambda k Qv digits j c hc hDigits t.1.number height node 0 t.1.number zero
    hJ hHeight hValid hPath hm hm.1 hz hSafe
  have hLift : W+primitive H≤B := Nat.add_le_add_left (hMono (by omega)) W
  have hf := hF.trans (Nat.mul_le_mul_left (524288*(M+1)) hLift)
  have hh := hD.trans (Nat.mul_le_mul_left (8388608*(height+1)*(M+1)) hLift)
  change t.2≤524288*(M+1)*B at hf
  change d.2≤8388608*(height+1)*(M+1)*B at hh
  have hCode := GeneralPaperQuantilePathPrice.work primitive hMono W d.1.path
  have hLen : d.1.path.length=height := descent_length true primitive W c digits j t.1.number height node 0 t.1.number zero
  rw [hLen] at hCode
  have hMeta : metadata primitive t.1.work d.1.work height≤8*primitive (4*H) := by
    dsimp only [d]
    rw [hd,ht,hc]
    exact GeneralPaperQuantileSearchControls.native_work primitive hMono m lambda k Qv digits j height hDigits node hHeight
  change t.2+d.2+(GeneralPaperQuantilePathPrice.run primitive W d.1.path).2+
    metadata primitive t.1.work d.1.work height+64*W≤_
  change _≤16777216*(height+1)*(M+1)*B+128*(height+1)*(W+primitive (8+2*(height+1)))
  dsimp only [B] at hf hh ⊢
  nlinarith only [hf,hh,hCode,hMeta,Nat.zero_le M,Nat.zero_le height]

theorem arithmetic_work (m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height) :
    (run false (fun _ => 1) 1 c digits j height node).2≤16777216*(height+1)*(measure m lambda k Qv+1)^2 := by
  let M := measure m lambda k Qv
  let t := total false (fun _ => 1) 1 c node
  let d := GeneralPaperQuantileDescentExecution.run false (fun _ => 1) 1 c digits j t.1.number height node 0 t.1.number zero
  have hf := GeneralPaperFreshMassPrice.arithmetic_work m lambda k Qv c hc 0 node
  have hd := GeneralPaperQuantileDescentArithmetic.work m lambda k Qv digits j c hc hDigits t.1.number height node 0 t.1.number zero
  have hp := GeneralPaperQuantilePathPrice.arithmetic_work d.1.path
  have hLen : d.1.path.length=height := descent_length false (fun _ => 1) 1 c digits j t.1.number height node 0 t.1.number zero
  rw [hLen] at hp
  have hMeta : metadata (fun _ => 1) t.1.work d.1.work height=8 := by rfl
  change t.2+d.2+(GeneralPaperQuantilePathPrice.run (fun _ => 1) 1 d.1.path).2+
    metadata (fun _ => 1) t.1.work d.1.work height+64≤_
  rw [hMeta]
  change t.2≤1048576*(M+1)^2 at hf
  change d.2≤8388608*(height+1)*(M+1)^2 at hd
  change _≤16777216*(height+1)*(M+1)^2
  have hOne : 1≤(M+1)^2 := by nlinarith only [Nat.zero_le M]
  have hScale := Nat.mul_le_mul_left (height+1) hOne
  have hTerm := Nat.mul_le_mul_right ((M+1)^2) (show 1≤height+1 by omega)
  simp only [Nat.mul_one] at hScale
  simp only [one_mul] at hTerm
  nlinarith only [hf,hd,hp,hOne,hScale,hTerm,Nat.zero_le height]

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run true primitive W c digits j height node).1=(run false (fun _ => 1) 1 c digits j height node).1 := by
  rw [data true primitive W m lambda k Qv digits j height c hc node hHeight hValid hPath,
    data false (fun _ => 1) 1 m lambda k Qv digits j height c hc node hHeight hValid hPath]

theorem bracket (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    let location := (run bits primitive W c digits j height node).1.location
    GeneralPaperQuantileSearch.cdf k node location≤(j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+GeneralPaperNormalizedMassError.delta k ∧
      (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-GeneralPaperNormalizedMassError.delta k≤GeneralPaperQuantileSearch.cdf k node (location+1) := by
  dsimp only
  rw [data bits primitive W m lambda k Qv digits j height c hc node hHeight hValid hPath,hc,hDigits]
  exact GeneralPaperQuantileSearch.search_bracket lambda k j height node hJ hHeight hValid hPath

end Blotto.GeneralPaperQuantileSearchPrice
