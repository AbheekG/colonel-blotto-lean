import Blotto.GeneralPaperRangeCounterPrice

/-! Full bit prices for the actual sparse traversal, with reached integral
windows and native output paths. Source-format and full-code words remain
separate. All metadata bounds derive from the same returned native result;
no input encoding, trace, child replay or calibration pass is executed.
-/
namespace Blotto.GeneralPaperRangeUpdateBitPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperRangeUpdateExecution GeneralPaperRangeGeometryPrice GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def nodeProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let L := GeneralPaperDecoderControls.operandWidth lambda
  2097152*(M+1)*(W+price H)+1024*(W+price L+price H)

theorem allowance (price : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    2097152*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))+
      14*price (GeneralPaperDecoderControls.operandWidth lambda)+
      10*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+320*W≤nodeProfile price W m lambda k Qv := by
  unfold nodeProfile
  dsimp only
  omega

theorem disjoint_price (d A B W P K : ℕ) (hd : d≤4*A+64*W) (hK : P+14*A+10*B+320*W≤K) : d+64*W≤1*K := by omega

theorem covered_price (d c r A B W P K : ℕ) (hd : d≤4*A+64*W) (hc : c≤4*A+64*W)
    (hr : r≤2*B+64*W) (hK : P+14*A+10*B+320*W≤K) : d+c+r+64*W≤1*K := by omega

theorem leaf_price (d c A B W P K : ℕ) (hd : d≤4*A+64*W) (hc : c≤4*A+64*W)
    (hK : P+14*A+10*B+320*W≤K) : d+c+64*W≤1*K := by omega

theorem combine (lp rp pp d c s z lv rv A B W P K : ℕ)
    (hl : lp≤lv*K) (hr : rp≤rv*K) (hp : pp≤P) (hd : d≤4*A+64*W) (hc : c≤4*A+64*W)
    (hs : s≤6*A+64*W) (hz : z≤10*B) (hK : P+14*A+10*B+320*W≤K) :
    lp+rp+pp+d+c+s+z+128*W≤(1+lv+rv)*K := by nlinarith

theorem partial_counters (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (lo hi : ℚ) (amount height : ℕ) (n : Node (height+1)) (start span : ℚ)
    (hD : ¬Disjoint start span lo hi) (hC : ¬Covered start span lo hi) :
    let left := run bits price W c lo hi amount height (leftChild n) start (span/2)
    let right := run bits price W c lo hi amount height (rightChild n) (start+span/2) (span/2)
    let joined := parent bits price W c left.1.node right.1.node
    (run bits price W c lo hi amount (height+1) n start span).1.work=left.1.work+right.1.work+joined.1.work+48 ∧
    (run bits price W c lo hi amount (height+1) n start span).1.visits=1+left.1.visits+right.1.visits := by
  dsimp only
  constructor <;> (conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC])

theorem span_positive (lambda height : ℕ) (start span : ℚ) (h : Window lambda height start span) : 0<span := by
  obtain ⟨_,_,hs,_⟩ := h
  rw [hs]
  positivity

theorem visited_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ)
    (hHeight : height≤lambda+1) (hWindow : Window lambda height start span) (hLo : Bounded lambda lo) (hHi : Bounded lambda hi)
    (hValid : Valid lambda k n)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span).node) :
    (run true price W c lo hi amount height n start span).2≤
      (run true price W c lo hi amount height n start span).1.visits*nodeProfile price W m lambda k Qv := by
  let A := price (GeneralPaperDecoderControls.operandWidth lambda)
  let B := price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
  let P := 2097152*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*(W+B)
  let K := nodeProfile price W m lambda k Qv
  have hK : P+14*A+10*B+320*W≤K := allowance price W m lambda k Qv
  have hPowers : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  induction height generalizing start span with
  | zero =>
    have hd := GeneralPaperRangeGeometryPrice.guard_work price hMono W lambda 0 start span hi lo hWindow hHi hLo
    have ht := GeneralPaperRangeGeometryPrice.guard_work price hMono W lambda 0 start span lo hi hWindow hLo hHi
    by_cases hD : Disjoint start span lo hi
    · conv_lhs => rw [run.eq_def,ite_eq_left hD]
      conv_rhs => rw [run.eq_def,ite_eq_left hD]
      exact disjoint_price _ A B W P K hd hK
    · by_cases hC : Covered start span lo hi
      · have hb := GeneralPaperRangeCounterPrice.covered_root_bound c.powers lambda k lo hi amount 0 n start span hD hC hOutput
        have hr := GeneralPaperRangeCounterPrice.raise_work price hMono W m lambda k Qv amount n hb
        conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        exact covered_price _ _ _ A B W P K hd ht hr hK
      · conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        exact leaf_price _ _ A B W P K hd ht hK
  | succ height ih =>
    have hd := GeneralPaperRangeGeometryPrice.guard_work price hMono W lambda (height+1) start span hi lo hWindow hHi hLo
    have ht := GeneralPaperRangeGeometryPrice.guard_work price hMono W lambda (height+1) start span lo hi hWindow hLo hHi
    by_cases hD : Disjoint start span lo hi
    · conv_lhs => rw [run.eq_def,ite_eq_left hD]
      conv_rhs => rw [run.eq_def,ite_eq_left hD]
      exact disjoint_price _ A B W P K hd hK
    · by_cases hC : Covered start span lo hi
      · have hb := GeneralPaperRangeCounterPrice.covered_root_bound c.powers lambda k lo hi amount (height+1) n start span hD hC hOutput
        have hr := GeneralPaperRangeCounterPrice.raise_work price hMono W m lambda k Qv amount n hb
        conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        exact covered_price _ _ _ A B W P K hd ht hr hK
      · let left := run true price W c lo hi amount height (leftChild n) start (span/2)
        let right := run true price W c lo hi amount height (rightChild n) (start+span/2) (span/2)
        let joined := parent true price W c left.1.node right.1.node
        have hPost := GeneralPaperRangeUpdateState.partial_children lambda k lo hi amount height n start span hD hC hValid
          (by rw [hPowers] at hOutput; exact hOutput)
        have hInput := child_validity lambda k n hValid
        have hWindows := child_windows lambda height start span hWindow
        have hl := ih (leftChild n) start (span/2) (by omega) hWindows.1 hInput.1 (by rw [hPowers]; exact hPost.2.2.1)
        have hr := ih (rightChild n) (start+span/2) (span/2) (by omega) hWindows.2 hInput.2 (by rw [hPowers]; exact hPost.2.2.2)
        have hld := GeneralPaperRangeUpdateExecution.data true price W m lambda k Qv c hc lo hi amount height (leftChild n) start (span/2)
          hInput.1 (by rw [hPowers]; exact hPost.2.2.1)
        have hrd := GeneralPaperRangeUpdateExecution.data true price W m lambda k Qv c hc lo hi amount height (rightChild n) (start+span/2) (span/2)
          hInput.2 (by rw [hPowers]; exact hPost.2.2.2)
        have hlv : Valid lambda k left.1.node := by rw [hld,hPowers]; exact hPost.1
        have hrv : Valid lambda k right.1.node := by rw [hrd,hPowers]; exact hPost.2.1
        have hlp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 left.1.node := by rw [hld,hPowers]; exact hPost.2.2.1
        have hrp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 right.1.node := by rw [hrd,hPowers]; exact hPost.2.2.2
        have hp := GeneralPaperParentCachePrice.work price hMono W m lambda k Qv c hc left.1.node right.1.node (by omega) hlv hrv hlp hrp
        have hs := GeneralPaperRangeGeometryPrice.split_work price hMono W lambda height start span hWindow hHeight
        have hb : (run true price W c lo hi amount (height+1) n start span).1.work≤GeneralPaperRangeCounterPrice.cap lambda k ∧
            (run true price W c lo hi amount (height+1) n start span).1.visits≤GeneralPaperRangeCounterPrice.cap lambda k := by
          rw [GeneralPaperRangeUpdateExecution.data true price W m lambda k Qv c hc lo hi amount (height+1) n start span hValid hOutput,hPowers]
          exact GeneralPaperRangeCounterPrice.native_bounds lambda k lo hi amount (height+1) n start span hHeight
            (span_positive lambda (height+1) start span hWindow)
        have parts := partial_counters true price W c lo hi amount height n start span hD hC
        rw [parts.1,parts.2] at hb
        have hm := GeneralPaperRangeCounterPrice.metadata_work price hMono left.1 right.1 joined.1 _ _ hb.1 hb.2
          (GeneralPaperRangeCounterPrice.operand_width m lambda k Qv)
        conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        exact combine left.2 right.2 joined.2 _ _ _ _ left.1.visits right.1.visits A B W P K hl hr hp hd ht hs hm hK

theorem linear_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ)
    (hHeight : height≤lambda+1) (hWindow : Window lambda height start span) (hLo : Bounded lambda lo) (hHi : Bounded lambda hi)
    (hValid : Valid lambda k n)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span).node) :
    (run true price W c lo hi amount height n start span).2≤(1+4*height)*nodeProfile price W m lambda k Qv := by
  have h := visited_work price hMono W m lambda k Qv c hc lo hi amount height n start span hHeight hWindow hLo hHi hValid hOutput
  rw [GeneralPaperRangeUpdateExecution.data true price W m lambda k Qv c hc lo hi amount height n start span hValid hOutput] at h
  exact h.trans (Nat.mul_le_mul_right _ (GeneralPaperIntervalUpdate.visits_linear c.powers lo hi amount height n start span
    (span_positive lambda height start span hWindow)))

theorem root_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1)
    (hLo : lo≤2^(lambda+1)) (hHi : hi≤2^(lambda+1)) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (GeneralPaperRangeRootPrice.run true price W c lo hi amount height n span).2≤
      (1+4*height)*nodeProfile price W m lambda k Qv+2*price (GeneralPaperDecoderControls.operandWidth lambda)+64*W := by
  have hOutput := GeneralPaperRangeRootPrice.grid_output_path m lambda k Qv c hc lo hi amount height n span hSpan hFinal
  have hWindow : Window lambda height 0 span := by rw [hSpan]; exact root_window lambda height hHeight
  have h := linear_work price hMono W m lambda k Qv c hc (lo:ℚ) hi amount height n 0 span hHeight hWindow
    ⟨lo,rfl,hLo⟩ ⟨hi,rfl,hHi⟩ hValid hOutput
  have hl := hMono (rational_word lambda (lo:ℚ) ⟨lo,rfl,hLo⟩)
  have hr := hMono (rational_word lambda (hi:ℚ) ⟨hi,rfl,hHi⟩)
  have hTotal := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h hl) hr) (64*W)
  change (run true price W c (lo:ℚ) hi amount height n 0 span).2+price (rationalWordWidth (lo:ℚ))+price (rationalWordWidth (hi:ℚ))+64*W≤_
  refine hTotal.trans_eq ?_
  ring

end Blotto.GeneralPaperRangeUpdateBitPrice
