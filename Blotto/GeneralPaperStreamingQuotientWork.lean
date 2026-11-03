import Blotto.GeneralPaperQuotientPhaseSpace

/-! Bit-operation budgets of the same fixed-register quotient program.
Each actually reached step charges arithmetic scratch prices and constant
word control/writes. Both traversals cost the actual adaptive depth.
-/
namespace Blotto.GeneralPaperStreamingQuotientWork
open GeneralPaperQuotientTraversal GeneralPaperQuotientRegisters GeneralPaperQuotientRegisterBounds
open GeneralPaperQuotientRegisterSpace
set_option autoImplicit false
set_option maxHeartbeats 8000000

def upCost (model : RationalCostModel) (W n scale : ℕ) : ℕ → ℕ → ℕ
  | 0,count => 32*W+upScratch model n ⟨scale,0,count⟩
  | fuel+1,count =>
    if n<scale then 32*W+upScratch model n ⟨scale,fuel+1,count⟩
    else upCost model W n (2*scale) fuel (count+1)+64*W+upScratch model n ⟨scale,fuel+1,count⟩

def downCost (model : RationalCostModel) (W scale : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_q,_r => 32*W
  | remaining+1,q,r =>
    let smaller := scale/2
    let qr := restore smaller (q,r)
    downCost model W smaller remaining qr.1 qr.2+96*W+downScratch model ⟨scale,remaining+1,q,r⟩

theorem up_work (model : RationalCostModel) (W n a fuel : ℕ) (s : UpState) (h : UpValid n a fuel s) :
    let F := W+model.rat (operandWord n a)
    upCost model W n s.scale s.fuel s.count+128*s.count*F≤128*((upValue n s).depth+1)*F := by
  let P := model.rat (operandWord n a)
  let F := W+P
  obtain ⟨scale,remaining,count⟩ := s
  induction remaining generalizing scale count with
  | zero =>
    have hs := up_scratch model n a fuel ⟨scale,0,count⟩ h
    change upCost model W n scale 0 count+128*count*F≤128*(count+1)*F
    change _≤3*P at hs
    unfold upCost
    dsimp only [F]
    nlinarith only [hs]
  | succ remaining ih =>
    have hs := up_scratch model n a fuel ⟨scale,remaining+1,count⟩ h
    change _≤3*P at hs
    by_cases hn : n<scale
    · have hStep : upStep n ⟨scale,remaining+1,count⟩=none := by simp only [upStep,ite_eq_left hn]
      rw [up_stop_value _ _ hStep]
      change upCost model W n scale (remaining+1) count+128*count*F≤128*(count+1)*F
      rw [upCost,ite_eq_left hn]
      dsimp only [F]
      nlinarith only [hs]
    · have hStep : upStep n ⟨scale,remaining+1,count⟩=some ⟨2*scale,remaining,count+1⟩ := by simp only [upStep,ite_eq_right hn]
      have hi := ih (2*scale) (count+1) (up_next n a fuel _ _ h hStep)
      rw [up_step_value _ _ _ hStep]
      rw [upCost,ite_eq_right hn]
      change upCost model W n (2*scale) remaining (count+1)+64*W+
        upScratch model n ⟨scale,remaining+1,count⟩+128*count*F≤
        128*((upValue n ⟨2*scale,remaining,count+1⟩).depth+1)*F
      change upCost model W n (2*scale) remaining (count+1)+128*(count+1)*F≤
        128*((upValue n ⟨2*scale,remaining,count+1⟩).depth+1)*F at hi
      have hWF : W≤F := Nat.le_add_right _ _
      have hPF : P≤F := Nat.le_add_left _ _
      nlinarith only [hi,hs,hWF,hPF]

theorem down_work (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (s : DownState) (h : DownValid n a fuel s) :
    downCost model W s.scale s.remaining s.quotient s.remainder≤256*(s.remaining+1)*(W+model.rat (operandWord n a)) := by
  let P := model.rat (operandWord n a)
  let F := W+P
  obtain ⟨scale,remaining,q,r⟩ := s
  induction remaining generalizing scale q r with
  | zero => change 32*W≤256*(0+1)*F; dsimp [F]; omega
  | succ remaining ih =>
    let next : DownState := ⟨scale/2,remaining,(restore (scale/2) (q,r)).1,(restore (scale/2) (q,r)).2⟩
    have hStep : downStep ⟨scale,remaining+1,q,r⟩=some next := rfl
    have hn := down_next n a fuel ha _ _ h hStep
    have hi := ih next.scale next.quotient next.remainder hn
    have hs := down_scratch model n a fuel ⟨scale,remaining+1,q,r⟩ h
    change _≤9*P at hs
    change downCost model W scale (remaining+1) q r≤256*(remaining+1+1)*F
    rw [downCost]
    change downCost model W next.scale remaining next.quotient next.remainder+
      96*W+downScratch model ⟨scale,remaining+1,q,r⟩≤256*(remaining+1+1)*F
    change downCost model W next.scale remaining next.quotient next.remainder≤256*(remaining+1)*F at hi
    have hWF : W≤F := Nat.le_add_right _ _
    have hPF : P≤F := Nat.le_add_left _ _
    nlinarith only [hi,hs,hWF,hPF]

def cost (model : RationalCostModel) (W n a fuel : ℕ) : ℕ :=
  let top := up n a fuel 0
  upCost model W n a fuel 0+downCost model W top.scale top.depth 0 n+96*W

theorem work (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) :
    cost model W n a fuel≤512*((GeneralPaperStreamingQuotient.run n a fuel).depth+1)*
      (W+model.rat (operandWord n a)) := by
  let F := W+model.rat (operandWord n a)
  have hu := up_work model W n a fuel ⟨a,fuel,0⟩ (up_initial n a fuel ha)
  have hd := down_work model W n a fuel ha (initialDown n a fuel) (down_initial n a fuel ha)
  change upCost model W n a fuel 0+128*0*F≤128*((up n a fuel 0).depth+1)*F at hu
  change downCost model W (up n a fuel 0).scale (up n a fuel 0).depth 0 n≤
    256*((up n a fuel 0).depth+1)*F at hd
  change upCost model W n a fuel 0+downCost model W (up n a fuel 0).scale (up n a fuel 0).depth 0 n+96*W≤
    512*((up n a fuel 0).depth+1)*F
  have hWF : W≤F := Nat.le_add_right _ _
  nlinarith only [hu,hd,hWF,Nat.zero_le ((up n a fuel 0).depth*F)]

def run (model : RationalCostModel) (W n a fuel : ℕ) :=
  (GeneralPaperStreamingQuotient.run n a fuel,cost model W n a fuel)

theorem data (model : RationalCostModel) (W n a fuel : ℕ) :
    (run model W n a fuel).1=GeneralPaperNaturalGrowingQuotient.run n a fuel :=
  GeneralPaperStreamingQuotient.data n a fuel

end Blotto.GeneralPaperStreamingQuotientWork
