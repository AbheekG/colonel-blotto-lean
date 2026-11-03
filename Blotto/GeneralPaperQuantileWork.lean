import Blotto.GeneralPaperQuantileSearch

/-! Single-path operation count, including virtual halving, exact scaled
comparisons and the final linear code fold. Primitive bit/storage calibration
is a separate ledger; this bound does not charge a whole-prefix query per level.
-/
namespace Blotto.GeneralPaperQuantileWork
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperIntervalCache
open GeneralPaperGlobalNodeQuery GeneralPaperQuantileDescent GeneralPaperQuantileSearch
set_option autoImplicit false
set_option maxHeartbeats 2500000

def massPrice (lambda k : ℕ) : ℕ :=
  (prepare lambda k).format.columns*(12*((prepare lambda k).format.fractionalBits+1)+82)+
    12*((prepare lambda k).format.fractionalBits+1)+92

def stepPrice (lambda k width : ℕ) : ℕ :=
  2*massPrice lambda k+8*(prepare lambda k).format.fractionalBits+
    12*((prepare lambda k).format.fractionalBits+1)+8*width+150

theorem child_work (lambda k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (storedMass : Number) :
    (leftMass (prepare lambda k) ancestor node storedMass).work≤massPrice lambda k ∧
      (rightMass (prepare lambda k) ancestor node storedMass).work≤massPrice lambda k := by
  cases node with
  | uniform h level => dsimp only [leftMass,rightMass,massPrice]; constructor <;> omega
  | branch level cached left right => exact ⟨fresh_work _ _ _ _,fresh_work _ _ _ _⟩

theorem run_work (lambda k width j s : ℕ) (storedTotal : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    (run (prepare lambda k) width j s storedTotal height node ancestor storedMass storedPrefix).work≤
      height*stepPrice lambda k width+8 := by
  induction height generalizing ancestor storedMass storedPrefix with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ height ih =>
    have hc := child_work lambda k ancestor node storedMass
    have ha := GeneralPaperDyadicAddition.add_work (prepare lambda k).format.unit
      (prepare lambda k).format.fractionalBits storedPrefix (leftMass (prepare lambda k) ancestor node storedMass).number
    have hCompare := GeneralPaperDyadicCompare.scaled_work width j storedTotal s
      (GeneralPaperDyadicAddition.add (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits
        storedPrefix (leftMass (prepare lambda k) ancestor node storedMass).number).number
    rw [run]
    split <;> dsimp only
    · have hi := ih (GeneralPaperIntervalLevels.leftChild node) (ancestor+offset node)
        (leftMass (prepare lambda k) ancestor node storedMass).number storedPrefix
      unfold stepPrice at *
      nlinarith
    · have hi := ih (GeneralPaperIntervalLevels.rightChild node) (ancestor+offset node)
        (rightMass (prepare lambda k) ancestor node storedMass).number
        (GeneralPaperDyadicAddition.add (prepare lambda k).format.unit (prepare lambda k).format.fractionalBits
          storedPrefix (leftMass (prepare lambda k) ancestor node storedMass).number).number
      unfold stepPrice at *
      nlinarith

theorem search_work (lambda k width j s height : ℕ) (node : Node height) :
    (search (prepare lambda k) width j s height node).work≤
      massPrice lambda k+height*(stepPrice lambda k width+8)+24 := by
  have hm := fresh_work lambda k 0 node
  have hr := run_work lambda k width j s (fresh (prepare lambda k) 0 node).number height node 0
    (fresh (prepare lambda k) 0 node).number zero
  change (fresh (prepare lambda k) 0 node).work+_+8*_+16≤_
  rw [path_length]
  dsimp only [massPrice] at *
  nlinarith

end Blotto.GeneralPaperQuantileWork
