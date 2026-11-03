import Blotto.GeneralPaperBatchUpdateExecution

/-! Full unit-arithmetic batch price. Every range call uses the retained
span and preparation cache; the final effect derives each successive input
and output state invariant. No phase-cost or validation oracle is supplied.
-/
namespace Blotto.GeneralPaperBatchUpdateArithmetic
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
open GeneralPaperBatchUpdateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def entryProfile (m lambda k Qv height : ℕ) : ℕ :=
  ((1+4*height)*GeneralPaperRangeUpdateArithmetic.nodeProfile m lambda k Qv+66)+262

theorem combine (u t R N : ℕ) (hu : u≤R) (ht : t≤N*(R+262)+64) :
    u+t+6+256≤(N+1)*(R+262)+64 := by nlinarith

theorem work (price : ℕ → ℕ) (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction) (hSpan : span=(2:ℚ)^height)
    (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run false price 1 c height span n entries).2≤entries.length*entryProfile m lambda k Qv height+64 := by
  have hPowers : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  induction entries generalizing n with
  | nil => simp only [GeneralPaperBatchUpdateExecution.run,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.mul_one,le_refl]
  | cons entry rest ih =>
    let updated := GeneralPaperRangeRootPrice.run false price 1 c entry.lo entry.hi entry.amount height n span
    let tail := run false price 1 c height span updated.1.node rest
    have hs := GeneralPaperBatchUpdateState.head_state lambda k height span n entry rest hSpan hValid hFinal
    have hu := GeneralPaperRangeRootPrice.grid_data false price 1 m lambda k Qv c hc entry.lo entry.hi entry.amount height n span hSpan hValid hs.1
    have hValidUpdated : Valid lambda k updated.1.node := by rw [hu,hPowers]; exact hs.2.1
    have hRestFinal : ∀ i<2^height,levelAt updated.1.node i+effect rest i≤GeneralPaperPowerPrecision.levelBound lambda k := by
      rw [hu,hPowers]
      exact hs.2.2
    have ht := ih updated.1.node hValidUpdated hRestFinal
    have hh := GeneralPaperRangeRootPrice.arithmetic_work price m lambda k Qv c hc entry.lo entry.hi entry.amount height n span hSpan hValid hs.1
    rw [GeneralPaperBatchUpdateExecution.run]
    dsimp only
    simp only [Bool.false_eq_true,ite_false,metadata_arithmetic,Nat.mul_one]
    exact combine updated.2 tail.2 _ rest.length hh ht

end Blotto.GeneralPaperBatchUpdateArithmetic
