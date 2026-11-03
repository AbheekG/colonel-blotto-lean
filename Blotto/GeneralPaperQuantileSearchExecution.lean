import Blotto.GeneralPaperQuantilePathPrice

/-! A root search shares one fresh total, one recursive descent and one
path fold. The known height supplies native length metadata without walking
the path again. Both models preserve the complete native search output.
-/
namespace Blotto.GeneralPaperQuantileSearchExecution
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def total (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    {height : ℕ} (node : Node height) : GeneralPaperDyadicMultiply.Result × ℕ :=
  if bits then GeneralPaperFreshMassPrice.run primitive W c 0 node else GeneralPaperFreshMassPrice.arithmetic c 0 node

def metadata (primitive : ℕ → ℕ) (totalWork descentWork height : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 8 height+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) totalWork descentWork+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (totalWork+descentWork) (8*height)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (totalWork+descentWork+8*height) 16

def run (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits j height : ℕ) (node : Node height) : GeneralPaperQuantileSearch.Output × ℕ :=
  let t := total bits primitive W c node
  let d := GeneralPaperQuantileDescentExecution.run bits primitive W c digits j t.1.number height node 0 t.1.number zero
  let code := GeneralPaperQuantilePathPrice.run primitive W d.1.path
  (⟨code.1,t.1.work+d.1.work+8*height+16,d.1.visits⟩,
    t.2+d.2+code.2+metadata primitive t.1.work d.1.work height+64*W)

theorem total_data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (node : Node height) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (total bits primitive W c node).1=fresh c.powers 0 node := by
  cases bits
  · exact GeneralPaperFreshMassPrice.arithmetic_data c 0 node
  · exact GeneralPaperFreshMassPrice.data primitive W m lambda k Qv c hc 0 node hValid hPath

theorem descent_length (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits j : ℕ) (total : Number) (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    (GeneralPaperQuantileDescentExecution.run bits primitive W c digits j total height node ancestor storedMass storedPrefix).1.path.length=height := by
  induction height generalizing ancestor storedMass storedPrefix with
  | zero => rfl
  | succ height ih =>
    rw [GeneralPaperQuantileDescentExecution.run]
    split <;> dsimp only [GeneralPaperQuantileDescentExecution.finish] <;> rw [List.length_cons,ih]

theorem data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run bits primitive W c digits j height node).1=
      GeneralPaperQuantileSearch.search c.powers digits j c.controls.source.summarySize height node := by
  let t := total bits primitive W c node
  have ht := total_data bits primitive W m lambda k Qv c hc node hValid hPath
  have hm : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) (trueMass k 0 node) t.1.number := by
    rw [ht,hc]
    exact fresh_bound lambda k 0 node hHeight hValid hPath
  have hz := (zero_bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)).1
  have hd := GeneralPaperQuantileDescentData.data bits primitive W m lambda k Qv digits j c hc t.1.number height node 0 t.1.number zero
    hHeight hValid hPath hm hz
  unfold run
  dsimp only
  rw [GeneralPaperQuantilePathPrice.data,hd,ht]
  unfold GeneralPaperQuantileSearch.search GeneralPaperQuantileDescent.code
  dsimp only
  rw [GeneralPaperQuantileDescent.path_length]

end Blotto.GeneralPaperQuantileSearchExecution
