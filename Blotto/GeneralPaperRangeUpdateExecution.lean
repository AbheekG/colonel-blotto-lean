import Blotto.GeneralPaperRangeUpdateState

/-! Sparse native range traversal with explicit operation prices. The two
models share guards, endpoints, selected recursive calls and all native
annotations. Parent recomputation uses the retained cache once. Counts and
prices are returned by the same recursion, without a trace or sum pass.
-/
namespace Blotto.GeneralPaperRangeUpdateExecution
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def guardCost (price : ℕ → ℕ) (W : ℕ) (start span a b : ℚ) : ℕ :=
  GeneralPaperRationalPrimitivePrice.binary price (fun x y => x+y) start span+
    price (RationalExpression.pairWidth a start)+price (RationalExpression.pairWidth (start+span) b)+64*W

def splitCost (price : ℕ → ℕ) (W height : ℕ) (start span : ℚ) : ℕ :=
  GeneralPaperRationalPrimitivePrice.binary price (fun x y => x/y) span 2+
    GeneralPaperRationalPrimitivePrice.binary price (fun x y => x+y) start (span/2)+
    GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x-y) (height+1) 1+64*W

def raiseCost (price : ℕ → ℕ) (W amount : ℕ) {height : ℕ} (n : Node height) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x+y) (offset n) amount+64*W

def metadataCost (price : ℕ → ℕ) {height : ℕ} (left right : GeneralPaperIntervalUpdate.Result height)
    (joined : GeneralPaperDyadicMultiply.Result) : ℕ :=
  GeneralPaperPowerTableBounds.metadataCost price left.work right.work joined.work+
    GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x+y) (left.work+right.work+joined.work) 48+
    GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x+y) 1 left.visits+
    GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x+y) (1+left.visits) right.visits

def parent (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    {height : ℕ} (left right : Node height) : GeneralPaperDyadicMultiply.Result × ℕ :=
  if bits then GeneralPaperParentCachePrice.run price W c left right else GeneralPaperParentCachePrice.arithmetic c left right

def run (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ) : GeneralPaperIntervalUpdate.Result height × ℕ :=
  let p := if bits then price else fun _ => 1
  let disjoint := guardCost p W start span hi lo
  if Disjoint start span lo hi then (⟨n,1,8⟩,disjoint+64*W) else
    let covered := guardCost p W start span lo hi
    if Covered start span lo hi then (⟨raiseRoot amount n,1,16⟩,disjoint+covered+raiseCost p W amount n+64*W) else
      match height with
      | 0 => (⟨n,1,8⟩,disjoint+covered+64*W)
      | height+1 =>
        let half := span/2
        let rightStart := start+half
        let left := run bits price W c lo hi amount height (leftChild n) start half
        let right := run bits price W c lo hi amount height (rightChild n) rightStart half
        let joined := parent bits price W c left.1.node right.1.node
        (⟨.branch (offset n) joined.1.number left.1.node right.1.node,
          1+left.1.visits+right.1.visits,left.1.work+right.1.work+joined.1.work+48⟩,
          left.2+right.2+joined.2+disjoint+covered+splitCost p W height start span+
            metadataCost p left.1 right.1 joined.1+128*W)
termination_by height

theorem parent_data (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (left right : Node height) (hl : Valid lambda k left) (hr : Valid lambda k right) :
    (parent bits price W c left right).1=GeneralPaperCachedMassJoin.recompute c.powers
      (offset left) (mass c.powers left) (offset right) (mass c.powers right) := by
  cases bits
  · exact GeneralPaperParentCachePrice.arithmetic_data m lambda k Qv c hc left right hl hr
  · exact GeneralPaperParentCachePrice.data price W m lambda k Qv c hc left right hl hr

theorem data (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ) (hValid : Valid lambda k n)
    (hOutput : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span).node) :
    (run bits price W c lo hi amount height n start span).1=GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span := by
  have hPowers : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  induction height generalizing start span with
  | zero =>
    by_cases hD : Disjoint start span lo hi
    · rw [run.eq_def,GeneralPaperIntervalUpdate.run.eq_def,ite_eq_left hD,ite_eq_left hD]
    · by_cases hC : Covered start span lo hi
      · rw [run.eq_def,GeneralPaperIntervalUpdate.run.eq_def,ite_eq_right hD,ite_eq_right hD,ite_eq_left hC,ite_eq_left hC]
      · rw [run.eq_def,GeneralPaperIntervalUpdate.run.eq_def,ite_eq_right hD,ite_eq_right hD,ite_eq_right hC,ite_eq_right hC]
  | succ height ih =>
    by_cases hD : Disjoint start span lo hi
    · rw [run.eq_def,GeneralPaperIntervalUpdate.run.eq_def,ite_eq_left hD,ite_eq_left hD]
    · by_cases hC : Covered start span lo hi
      · rw [run.eq_def,GeneralPaperIntervalUpdate.run.eq_def,ite_eq_right hD,ite_eq_right hD,ite_eq_left hC,ite_eq_left hC]
      · have hPost := GeneralPaperRangeUpdateState.partial_children lambda k lo hi amount height n start span hD hC hValid
          (by rw [hPowers] at hOutput; exact hOutput)
        have hInput := GeneralPaperGlobalNodeQuery.child_validity lambda k n hValid
        have hLeft := ih (leftChild n) start (span/2) hInput.1 (by rw [hPowers]; exact hPost.2.2.1)
        have hRight := ih (rightChild n) (start+span/2) (span/2) hInput.2 (by rw [hPowers]; exact hPost.2.2.2)
        rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        dsimp only
        rw [hLeft,hRight]
        have hp := parent_data bits price W m lambda k Qv c hc
          (GeneralPaperIntervalUpdate.run c.powers lo hi amount height (leftChild n) start (span/2)).node
          (GeneralPaperIntervalUpdate.run c.powers lo hi amount height (rightChild n) (start+span/2) (span/2)).node
          (by rw [hPowers]; exact hPost.1) (by rw [hPowers]; exact hPost.2.1)
        rw [hp]
        conv_rhs => rw [GeneralPaperIntervalUpdate.run.eq_def,ite_eq_right hD,ite_eq_right hC]
        cases n <;> rfl

end Blotto.GeneralPaperRangeUpdateExecution
