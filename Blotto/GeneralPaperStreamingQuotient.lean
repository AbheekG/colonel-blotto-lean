import Blotto.GeneralPaperQuotientTraversal

/-! Two tail traversals refine the exact existing adaptive quotient.
The result retains quotient/remainder/depth/work, while no divisor stack
is part of the executable data. Halving is exact on constructed powers.
-/
namespace Blotto.GeneralPaperStreamingQuotient
open GeneralPaperQuotientTraversal
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem down_data (n a fuel : ℕ) :
    let native := GeneralPaperNaturalGrowingQuotient.run n a fuel
    down (a*2^native.depth) native.depth (0,n)=(native.quotient,native.remainder) := by
  induction fuel generalizing a with
  | zero => simp only [GeneralPaperNaturalGrowingQuotient.run,down]
  | succ fuel ih =>
    rw [GeneralPaperNaturalGrowingQuotient.run]
    split
    · simp only [down]
    · have hi := ih (2*a)
      dsimp only
      have scale (depth : ℕ) : a*2^(depth+1)=(2*a)*2^depth := by rw [pow_succ]; ring
      split
      · rename_i hBit
        dsimp only
        rw [down_last,scale,hi]
        simp only [restore,ite_eq_left hBit]
      · rename_i hBit
        dsimp only
        rw [down_last,scale,hi]
        simp only [restore,ite_eq_right hBit]

def run (n a fuel : ℕ) : GeneralPaperNaturalGrowingQuotient.Result :=
  let top := up n a fuel 0
  let qr := down top.scale top.depth (0,n)
  ⟨qr.1,qr.2,top.depth,14*top.depth+4⟩

theorem data (n a fuel : ℕ) : run n a fuel=GeneralPaperNaturalGrowingQuotient.run n a fuel := by
  have ht := up_data n a fuel 0
  simp only [Nat.zero_add] at ht
  have hq := down_data n a fuel
  have hw := (GeneralPaperNaturalGrowingQuotient.counters n a fuel).1
  unfold run
  dsimp only
  rw [ht.1,ht.2,hq,←hw]

theorem rational_data (n a fuel : ℕ) :
    GeneralPaperNaturalGrowingQuotient.lift (run n a fuel)=GeneralPaperGrowingQuotient.run (n:ℚ) (a:ℚ) fuel := by
  rw [data]
  exact GeneralPaperNaturalGrowingQuotient.data n a fuel

theorem exact_halving (a depth : ℕ) :
    (((a*2^(depth+1))/2:ℕ):ℚ)=((a*2^(depth+1):ℕ):ℚ)/2 := by
  rw [halve]
  have he : a*2^(depth+1)=2*(a*2^depth) := by rw [pow_succ]; ring
  rw [he]
  push_cast
  ring

theorem depth_and_work (n a fuel : ℕ) :
    (run n a fuel).depth≤fuel ∧ (run n a fuel).work=14*(run n a fuel).depth+4 := by
  rw [data]
  have hh := GeneralPaperNaturalGrowingQuotient.counters n a fuel
  exact ⟨hh.2,hh.1⟩

end Blotto.GeneralPaperStreamingQuotient
