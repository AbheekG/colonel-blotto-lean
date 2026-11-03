import Blotto.GeneralPaperMidpointQueryBits

/-! Actual cached cell location followed by the inclusive root query.
Constructed cache and returned cell facts discharge every root-query premise.
The returned native classifier root is exact; original rational precision B
and the simultaneous control-word/temporary-space joins remain explicit.
-/
namespace Blotto.GeneralPaperCachedRootQueryBits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    (GeneralPaperBoundedQuotient.Result × GeneralPaperMidpointQuery.Result) × ℕ :=
  let location := GeneralPaperProxyQuotientPrice.run model W c b
  let root := GeneralPaperMidpointQueryBits.run model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)
  ((location.1,root.1),location.2+root.2+64*W)

theorem root_data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) :
    (run model W c b).1.2=GeneralPaperProxyRootQuery.lookup c.proxy.H c.proxy.Qg
      (GeneralPaperProxyQuotient.locate m k (b:ℝ)).quotient (c.proxy.gridBits+3) := by
  have hq := congrArg GeneralPaperProxyQuotient.Result.quotient
    (GeneralPaperProxyQuotientPrice.real_data model W m k c hc b)
  change (GeneralPaperProxyQuotientPrice.run model W c b).1.quotient=
    (GeneralPaperProxyQuotient.locate m k (b:ℝ)).quotient at hq
  simp only [run,GeneralPaperMidpointQueryBits.closed_data,hq]

theorem classifier_root (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) :
    (run model W c b).1.2.fraction=(GeneralPaperProxyClassifier.classify m k (b:ℝ)).root := by
  rw [root_data model W m k c hc b,hc]
  rfl

def profile (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  256*(c.proxy.gridBits+2)*(W+model.rat (GeneralPaperProxyQuotientPrice.envelope c B))+
  2097152*(c.proxy.gridBits+6)*(W+model.rat
    (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+64*W

theorem work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (run model W c b).2≤profile model W c B := by
  have hl := GeneralPaperProxyQuotientPrice.bounded_work model W m k c hc b hb B hB
  have hCell := (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  have hH : 0<c.proxy.H := by rw [hc]; exact GeneralPaperProxyParameters.H_positive m k
  have hQ : 0<c.proxy.Qg := by rw [hc]; exact GeneralPaperProxyParameters.grid_positive m k
  have hPower : 8*c.proxy.Qg=2^(c.proxy.gridBits+3) := by rw [hc]; exact GeneralPaperProxyClassifier.grid_dyadic m k
  have hr := GeneralPaperMidpointQueryBits.work model W c.proxy.H c.proxy.Qg
    (GeneralPaperProxyQuotientPrice.run model W c b).1.quotient (c.proxy.gridBits+3) true hH hQ hCell hPower
  change (GeneralPaperProxyQuotientPrice.run model W c b).2+
    (GeneralPaperMidpointQueryBits.run model W true c.proxy.H c.proxy.Qg
      (GeneralPaperProxyQuotientPrice.run model W c b).1.quotient (c.proxy.gridBits+3)).2+64*W≤_
  change _≤256*(c.proxy.gridBits+2)*(W+model.rat (GeneralPaperProxyQuotientPrice.envelope c B))+
    2097152*(c.proxy.gridBits+6)*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+64*W
  have he : c.proxy.gridBits+3+3=c.proxy.gridBits+6 := by omega
  rw [he] at hr
  exact Nat.add_le_add_right (Nat.add_le_add hl hr) (64*W)

end Blotto.GeneralPaperCachedRootQueryBits
