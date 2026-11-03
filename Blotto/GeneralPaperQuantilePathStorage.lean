import Blotto.GeneralPaperQuantileTraversalStorage

/-! Live integer accumulators of the one native path fold. Ancestor frames
are conservatively retained; path tails are borrowed. The known tree height
bounds every accumulator, with no length or representation pass at runtime. -/
namespace Blotto.GeneralPaperQuantilePathStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def peak (W : ℕ) : List Bool → ℕ → ℕ
  | [],acc => (1+binaryWordWidth acc)+64*W
  | bit::tail,acc =>
    let next := 2*acc+if bit then 1 else 0
    (1+binaryWordWidth acc)+(1+binaryWordWidth (2*acc))+
      (1+binaryWordWidth next)+256*W+peak W tail next

theorem fold_bound (W height : ℕ) (path : List Bool) (visited acc : ℕ)
    (hh : visited+path.length≤height) (ha : acc<2^visited) :
    peak W path acc≤(path.length+1)*(3*(height+3)+256*W) := by
  induction path generalizing visited acc with
  | nil =>
    have hPow := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show visited≤height+1 by simpa using hh.trans (Nat.le_add_right height 1))
    have hw := GeneralPaperCFOperandPrice.small_word (height+1) acc (ha.trans_le hPow)
    change (1+binaryWordWidth acc)+64*W≤(0+1)*(3*(height+3)+256*W)
    omega
  | cons bit tail ih =>
    let digit : ℕ := if bit then 1 else 0
    have hd : digit≤1 := by dsimp [digit]; cases bit <;> decide
    have hNext : 2*acc+digit<2^(visited+1) := by rw [pow_succ]; omega
    have hVisited : visited+1+tail.length≤height := by simp only [List.length_cons] at hh; omega
    have hc := ih (visited+1) (2*acc+digit) hVisited hNext
    have hPow := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show visited+1≤height+1 by omega)
    have hn := hNext.trans_le hPow
    have haW := GeneralPaperCFOperandPrice.small_word (height+1) acc (by omega : acc<2^(height+1))
    have hdW := GeneralPaperCFOperandPrice.small_word (height+1) (2*acc) (by omega : 2*acc<2^(height+1))
    have hnW := GeneralPaperCFOperandPrice.small_word (height+1) (2*acc+digit) hn
    change (1+binaryWordWidth acc)+(1+binaryWordWidth (2*acc))+(1+binaryWordWidth (2*acc+digit))+
      256*W+peak W tail (2*acc+digit)≤(tail.length+1+1)*(3*(height+3)+256*W)
    nlinarith only [hc,haW,hdW,hnW]

theorem bounded (W : ℕ) (path : List Bool) :
    peak W path 0≤(path.length+1)*(3*(path.length+3)+256*W) :=
  fold_bound W path.length path 0 0 (by simp) (by decide)

theorem output (path : List Bool) :
    1+binaryWordWidth (GeneralPaperQuantilePath.encode path)≤path.length+2 := by
  have h := GeneralPaperQuantilePath.index_bound path
  rw [←GeneralPaperQuantilePath.encode_index] at h
  have hw := GeneralPaperCFOperandPrice.small_word path.length _ h
  omega

end Blotto.GeneralPaperQuantilePathStorage
