import Blotto.GeneralPaperSelectionPrepared

/-! Complete constant-size selection bit price. One prepared point record
and one root value are reused by the ordered seven tests and branch writes.
Every natural/rational operand is bounded from Q and input precision B.
-/
namespace Blotto.GeneralPaperSelectionBits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rootWork (model : RationalCostModel) (root : Option Farey.Fraction) : ℕ := match root with
  | none => 0
  | some f => model.rat (rationalWordWidth (f.num:ℚ))+model.rat (rationalWordWidth (f.den:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (f.num:ℚ) (f.den:ℚ)

def testsWork (model : RationalCostModel) (b : ℚ) (p : GeneralPaperSelectionPoints.Points) (root : Option Farey.Fraction) : ℕ :=
  GeneralPaperBoundedQuotient.primitivePrice model b p.lower+
    2*GeneralPaperBoundedQuotient.primitivePrice model b
      (match root with | none => p.middle | some f => f.value)

theorem root_work (model : RationalCostModel) (Q B : ℕ) (root : Option Farey.Fraction)
    (hRoot : ∀ f,root=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    rootWork model root≤4*model.rat (GeneralPaperSelectionPoints.width Q B) := by
  cases hs : root with
  | none => exact Nat.zero_le _
  | some f =>
    have hf := hRoot f hs
    obtain ⟨hn,hd,hv⟩ := GeneralPaperSelectionPoints.root_words Q B f hf.1 hf.2
    have c1 := model.monotone hn
    have c2 := model.monotone hd
    have c3 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
      (f.num:ℚ) (f.den:ℚ) (GeneralPaperSelectionPoints.width Q B) hn hd hv
    change model.rat (rationalWordWidth (f.num:ℚ))+model.rat (rationalWordWidth (f.den:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (f.num:ℚ) (f.den:ℚ)≤_
    omega

theorem tests_work (model : RationalCostModel) (Q j B : ℕ) (b : ℚ) (root : Option Farey.Fraction)
    (hQ : 0<Q) (hj : j<Q) (hB : RationalHeight b B)
    (hRoot : ∀ f,root=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    testsWork model b (GeneralPaperSelectionPoints.prepare Q j) root≤
      3*model.rat (GeneralPaperSelectionPoints.width Q B) := by
  obtain ⟨hb,_,_,_,_,_,hl,_,hm⟩ := GeneralPaperSelectionPoints.rational_words Q j B b hQ hj hB
  have c1 := GeneralPaperBoundedQuotient.primitivePrice_le model b (GeneralPaperSelectionPoints.prepare Q j).lower
    (GeneralPaperSelectionPoints.width Q B) hb hl
  cases hs : root with
  | none =>
    have c2 := GeneralPaperBoundedQuotient.primitivePrice_le model b (GeneralPaperSelectionPoints.prepare Q j).middle
      (GeneralPaperSelectionPoints.width Q B) hb hm
    change GeneralPaperBoundedQuotient.primitivePrice model b (GeneralPaperSelectionPoints.prepare Q j).lower+
      2*GeneralPaperBoundedQuotient.primitivePrice model b (GeneralPaperSelectionPoints.prepare Q j).middle≤_
    omega
  | some f =>
    have hf := hRoot f hs
    have hv := (GeneralPaperSelectionPoints.root_words Q B f hf.1 hf.2).2.2
    have c2 := GeneralPaperBoundedQuotient.primitivePrice_le model b f.value (GeneralPaperSelectionPoints.width Q B) hb hv
    change GeneralPaperBoundedQuotient.primitivePrice model b (GeneralPaperSelectionPoints.prepare Q j).lower+
      2*GeneralPaperBoundedQuotient.primitivePrice model b f.value≤_
    omega

def run (model : RationalCostModel) (W Q j : ℕ) (hQ : 0<Q) (b : ℚ) (root : Option Farey.Fraction) :
    GeneralPaperProxySelection.Selected × ℕ :=
  let points := GeneralPaperSelectionPointsPrice.run model W Q j
  (GeneralPaperSelectionPrepared.choose Q j hQ points.1 (GeneralPaperSelectionPointsPrice.data model W Q j) b root,
    points.2+rootWork model root+testsWork model b points.1 root+128*W)

theorem data (model : RationalCostModel) (W Q j : ℕ) (hQ : 0<Q) (b : ℚ) (root : Option Farey.Fraction) :
    (run model W Q j hQ b root).1=GeneralPaperProxySelection.select Q j hQ (b:ℝ) root :=
  GeneralPaperSelectionPrepared.data Q j hQ _ (GeneralPaperSelectionPointsPrice.data model W Q j) b root

theorem work (model : RationalCostModel) (W Q j B : ℕ) (hQ : 0<Q) (b : ℚ) (root : Option Farey.Fraction)
    (hj : j<Q) (hB : RationalHeight b B)
    (hRoot : ∀ f,root=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    (run model W Q j hQ b root).2≤512*(W+model.rat (GeneralPaperSelectionPoints.width Q B)) := by
  have hp := GeneralPaperSelectionPointsPrice.work model W Q j B b hQ hj hB
  have hr := root_work model Q B root hRoot
  have ht := tests_work model Q j B b root hQ hj hB hRoot
  change (GeneralPaperSelectionPointsPrice.run model W Q j).2+rootWork model root+
    testsWork model b (GeneralPaperSelectionPoints.prepare Q j) root+128*W≤_
  omega

end Blotto.GeneralPaperSelectionBits
