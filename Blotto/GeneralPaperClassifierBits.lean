import Blotto.GeneralPaperClassifierRootBounds

/-! Complete cached classifier bit execution on a rational original budget.
Location, root query and seven-branch selection execute once. Reconstruct
the full native classifier annotation from their returned records, without
replaying parameter construction. Control capacity/space joins are separate.
-/
namespace Blotto.GeneralPaperClassifierBits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hQ : 0<c.proxy.Qg) (b : ℚ) : GeneralPaperProxyClassifier.Result × ℕ :=
  let queried := GeneralPaperCachedRootQueryBits.run model W c b
  let selected := GeneralPaperSelectionBits.run model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction
  (⟨queried.1.1.quotient,queried.1.2.fraction,selected.1,
    c.proxy.work+queried.1.1.work+queried.1.2.work+selected.1.work+24⟩,
    queried.2+selected.2+64*W)

theorem data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) :
    (run model W c hQ b).1=GeneralPaperProxyClassifier.classify m k (b:ℝ) := by
  subst c
  have hLoc := GeneralPaperProxyQuotientPrice.real_data model W m k
    (GeneralPaperPrecallCachePrice.specification m k) rfl b
  have hQuot := congrArg GeneralPaperProxyQuotient.Result.quotient hLoc
  have hWork := congrArg GeneralPaperProxyQuotient.Result.work hLoc
  change (GeneralPaperProxyQuotientPrice.run model W (GeneralPaperPrecallCachePrice.specification m k) b).1.quotient=
    (GeneralPaperProxyQuotient.locate m k (b:ℝ)).quotient at hQuot
  change (GeneralPaperProxyQuotientPrice.run model W (GeneralPaperPrecallCachePrice.specification m k) b).1.work=
    (GeneralPaperProxyQuotient.locate m k (b:ℝ)).work at hWork
  unfold run
  dsimp only
  rw [GeneralPaperSelectionBits.data,GeneralPaperCachedRootQueryBits.root_data model W m k _ rfl b]
  dsimp only [GeneralPaperCachedRootQueryBits.run]
  rw [hQuot,hWork]
  rfl

def profile (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) : ℕ :=
  GeneralPaperCachedRootQueryBits.profile model W c B+
    512*(W+model.rat (GeneralPaperSelectionPoints.width c.proxy.Qg B))+64*W

theorem work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ)
    (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (run model W c hQ b).2≤profile model W c B := by
  have hr := GeneralPaperCachedRootQueryBits.work model W m k c hc b hb B hB
  have hRoot := GeneralPaperClassifierRootBounds.root_bounds model W m k c hc b hb
  have hCell := (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  have hs := GeneralPaperSelectionBits.work model W c.proxy.Qg
    (GeneralPaperCachedRootQueryBits.run model W c b).1.1.quotient B hQ b
    (GeneralPaperCachedRootQueryBits.run model W c b).1.2.fraction hCell hB hRoot
  change (GeneralPaperCachedRootQueryBits.run model W c b).2+
    (GeneralPaperSelectionBits.run model W c.proxy.Qg (GeneralPaperCachedRootQueryBits.run model W c b).1.1.quotient
      hQ b (GeneralPaperCachedRootQueryBits.run model W c b).1.2.fraction).2+64*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add hr hs) (64*W)

end Blotto.GeneralPaperClassifierBits
