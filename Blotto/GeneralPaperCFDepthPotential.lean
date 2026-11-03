import Blotto.GeneralPaperMidpointComplete

/-! Amortize the actual adaptive quotient depths through the Euclidean
numerator's word width. The word widths occur only in proofs. Each division
loses enough potential to pay its depth apart from a constant per step, so
summing full-width division caps is unnecessary.
-/
namespace Blotto.GeneralPaperCFDepthPotential
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFAdvanceData
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem division_depth_width (n d fuel : ℕ) (hd : 0<d) (hOrder : d≤n) :
    (GeneralPaperConstructedNatDivision.run n d fuel).depth+binaryWordWidth d≤binaryWordWidth n+1 := by
  let depth := (GeneralPaperConstructedNatDivision.run n d fuel).depth
  have hScale : d*2^(depth-1)≤n := by
    by_cases hz : depth=0
    · simpa only [hz,Nat.zero_sub,pow_zero,Nat.mul_one] using hOrder
    · have hp : 0<depth := by omega
      have he := GeneralPaperGrowingQuotient.depth_scale n d (by exact_mod_cast hd) fuel hp
      have hn : d*2^(depth-1)≤n := by exact_mod_cast he
      exact hn
  have hN : 0<n := hd.trans_le hOrder
  have hLow : 2^d.log2≤d := (Nat.le_log2 hd.ne').mp le_rfl
  have hp := (Nat.mul_le_mul_right (2^(depth-1)) hLow).trans hScale
  rw [←pow_add] at hp
  have hLog := (Nat.le_log2 hN.ne').mpr hp
  change depth+binaryWordWidth d≤binaryWordWidth n+1
  unfold binaryWordWidth
  omega

theorem advance_depth_potential (D width : ℕ) (s : State) (hOrder : s.denominator≤s.numerator) :
    (advance D (width+2) s).1.quotientDepth+binaryWordWidth (advance D (width+2) s).1.numerator+s.steps≤
      s.quotientDepth+binaryWordWidth s.numerator+(advance D (width+2) s).1.steps := by
  by_cases hz : s.denominator=0
  · simp [advance,hz]
  · have hd : 0<s.denominator := by omega
    have he := division_depth_width s.numerator s.denominator (width+2) hd hOrder
    simp only [advance,ite_eq_right hz]
    split
    · split <;> dsimp only <;> omega
    · dsimp only
      omega

theorem run_depth_potential (D width fuel : ℕ) (s : State) (hPair : PairBound width s) (hOrder : s.denominator≤s.numerator) :
    (run D (width+2) fuel s).quotientDepth+binaryWordWidth (run D (width+2) fuel s).numerator+s.steps≤
      s.quotientDepth+binaryWordWidth s.numerator+(run D (width+2) fuel s).steps := by
  induction fuel generalizing s with
  | zero => exact le_rfl
  | succ fuel ih =>
    have he := advance_depth_potential D width s hOrder
    dsimp only [run]
    split
    · have hh := ih _ (advance_pair_bound D width s hPair) (euclidean_order D width s hPair hOrder)
      omega
    · exact he

theorem advance_step_count (D divisionFuel : ℕ) (s : State) : (advance D divisionFuel s).1.steps≤s.steps+1 := by
  dsimp only [advance]
  split
  · dsimp only
    omega
  · split
    · split <;> dsimp only <;> omega
    · dsimp only
      omega

theorem run_step_count (D divisionFuel fuel : ℕ) (s : State) : (run D divisionFuel fuel s).steps≤s.steps+fuel := by
  induction fuel generalizing s with
  | zero => simp only [run,Nat.add_zero,le_refl]
  | succ fuel ih =>
    have he := advance_step_count D divisionFuel s
    dsimp only [run]
    split
    · have hh := ih (advance D divisionFuel s).1
      omega
    · omega

theorem advance_depth_eq (D divisionFuel : ℕ) (s : State) (hd : 0<s.denominator) :
    (advance D divisionFuel s).1.quotientDepth=s.quotientDepth+
      (GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel).depth := by
  simp only [advance,ite_eq_right hd.ne']
  split
  · split <;> rfl
  · rfl

end Blotto.GeneralPaperCFDepthPotential
