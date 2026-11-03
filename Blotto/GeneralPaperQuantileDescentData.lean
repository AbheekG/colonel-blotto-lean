import Blotto.GeneralPaperQuantileDescentExecution

/-! Both priced executions return every native path/work/visits field.
Validity, path caps and the actual mass certificate propagate down the
selected branch. These are proofs about one run, not a replay of descent.
-/
namespace Blotto.GeneralPaperQuantileDescentData
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileDescentExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem step_data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits j ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass) (hPrefix : Normal c.powers.format.unit storedPrefix) :
    (step bits primitive W c digits j ancestor node total storedMass storedPrefix).1=
      GeneralPaperQuantileStepPrice.specification c digits j ancestor node total storedMass storedPrefix := by
  cases bits
  · exact GeneralPaperQuantileStepPrice.arithmetic_data m lambda k Qv digits j ancestor c hc node total storedMass storedPrefix
      hHeight hValid hPath hMass hPrefix
  · exact GeneralPaperQuantileStepPrice.data primitive W m lambda k Qv digits j ancestor c hc node total storedMass storedPrefix
      hHeight hValid hPath hMass hPrefix

theorem right_data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (node : Node (height+1)) (storedMass : Number) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node) :
    (right bits primitive W c ancestor node storedMass).1=GeneralPaperQuantileDescent.rightMass c.powers ancestor node storedMass := by
  cases bits
  · exact GeneralPaperQuantileChildPrice.arithmetic_data true c ancestor node storedMass
  · exact GeneralPaperQuantileChildPrice.data true primitive W m lambda k Qv c hc ancestor node storedMass hValid hPath

theorem data (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits j : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (total : Number) (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix) :
    (run bits primitive W c digits j total height node ancestor storedMass storedPrefix).1=
      GeneralPaperQuantileDescent.run c.powers digits j c.controls.source.summarySize total height node ancestor storedMass storedPrefix := by
  induction height generalizing ancestor storedMass storedPrefix with
  | zero => rfl
  | succ height ih =>
    have hChildren := child_validity lambda k node hValid
    have hPaths := child_paths _ ancestor node hPath
    have hL := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hR := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hLC : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
        (trueMass k (ancestor+offset node) (leftChild node))
        (GeneralPaperQuantileDescent.leftMass c.powers ancestor node storedMass).number := by rw [hc]; exact hL
    have hRC : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
        (trueMass k (ancestor+offset node) (rightChild node))
        (GeneralPaperQuantileDescent.rightMass c.powers ancestor node storedMass).number := by rw [hc]; exact hR
    have hThrough : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit
        (GeneralPaperDyadicAddition.add c.powers.format.unit c.powers.format.fractionalBits storedPrefix
          (GeneralPaperQuantileDescent.leftMass c.powers ancestor node storedMass).number).number := by
      rw [hc]
      exact GeneralPaperDyadicAddition.add_normal _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hPrefix hL.1
    have hp : Normal c.powers.format.unit storedPrefix := by rw [hc]; exact hPrefix
    have hs := step_data bits primitive W m lambda k Qv digits j ancestor c hc node total storedMass storedPrefix
      hHeight hValid hPath hMass hp
    have hr := right_data bits primitive W m lambda k Qv ancestor c hc node storedMass hValid hPath
    rw [run,GeneralPaperQuantileDescent.run]
    dsimp only
    rw [hs]
    dsimp only [GeneralPaperQuantileStepPrice.specification]
    split
    · rename_i hBranch
      simp only [hBranch,finish,ite_true]
      rw [ih (leftChild node) (ancestor+offset node) _ storedPrefix (by omega) hChildren.1 hPaths.1 hLC hPrefix]
      simp only [Nat.add_zero]
    · rename_i hBranch
      simp only [hBranch,finish,ite_false,Bool.false_eq_true]
      rw [hr]
      rw [ih (rightChild node) (ancestor+offset node) _ _ (by omega) hChildren.2 hPaths.2 hRC hThrough]

end Blotto.GeneralPaperQuantileDescentData
