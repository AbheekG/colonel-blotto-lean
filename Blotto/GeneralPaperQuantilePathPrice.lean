import Blotto.GeneralPaperQuantileDescentBits

/-! One linear path fold constructs the returned code. Its integer word
can contain one bit per level and is priced separately from the much smaller
stored mantissa/exponent words. Every reached accumulator is bounded.
-/
namespace Blotto.GeneralPaperQuantilePathPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def fold (primitive : ℕ → ℕ) (W : ℕ) : List Bool → ℕ → ℕ × ℕ
  | [],acc => (acc,16*W)
  | bit::tail,acc =>
    let doubled := 2*acc
    let digit := if bit then 1 else 0
    let next := doubled+digit
    let rest := fold primitive W tail next
    (rest.1,rest.2+32*W+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 acc+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) doubled digit)

def run (primitive : ℕ → ℕ) (W : ℕ) (path : List Bool) : ℕ × ℕ := fold primitive W path 0

theorem fold_data (primitive : ℕ → ℕ) (W : ℕ) (path : List Bool) (acc : ℕ) :
    (fold primitive W path acc).1=path.foldl (fun acc bit => 2*acc+if bit then 1 else 0) acc := by
  induction path generalizing acc with
  | nil => rfl
  | cons bit tail ih => simpa only [fold,List.foldl_cons] using ih (2*acc+if bit then 1 else 0)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (path : List Bool) :
    (run primitive W path).1=GeneralPaperQuantilePath.encode path := fold_data primitive W path 0

theorem fold_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W height : ℕ)
    (path : List Bool) (visited acc : ℕ) (hHeight : visited+path.length≤height) (hAcc : acc<2^visited) :
    (fold primitive W path acc).2≤64*(path.length+1)*(W+primitive (8+2*(height+1))) := by
  let N := 2^(height+1)
  let L := 8+2*(height+1)
  have hWord : 1+binaryWordWidth N≤L := by
    have hh := GeneralPaperNatPowerOperands.power_width 2 (height+1)
    have h2 : binaryWordWidth 2=2 := by decide
    dsimp [N,L]; rw [h2] at hh; omega
  induction path generalizing visited acc with
  | nil =>
    change 16*W≤64*(0+1)*(W+primitive L)
    omega
  | cons bit tail ih =>
    let digit : ℕ := if bit then 1 else 0
    have hDigit : digit≤1 := by dsimp [digit]; cases bit <;> decide
    have hNext : 2*acc+digit<2^(visited+1) := by rw [pow_succ]; omega
    have hPow : 2^(visited+1)≤N := Nat.pow_le_pow_right (by decide : 0<2) (by dsimp only [List.length_cons] at hHeight; omega)
    have hNextN : 2*acc+digit≤N := hNext.le.trans hPow
    have hAccN : acc≤N := by omega
    have h2 : 2≤N := by
      have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤height+1 by omega)
      simpa only [pow_one] using hh
    have hm := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) 2 acc N
      h2 hAccN (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hWord))
    have ha := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) (2*acc) digit N
      (by omega) (by omega) hNextN).trans (Nat.mul_le_mul_left 2 (hMono hWord))
    have hi := ih (visited+1) (2*acc+digit) (by dsimp only [List.length_cons] at hHeight; omega) hNext
    change (fold primitive W tail (2*acc+digit)).2+32*W+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 acc+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (2*acc) digit≤
        64*(tail.length+1+1)*(W+primitive L)
    change _≤64*(tail.length+1)*(W+primitive L) at hi
    nlinarith only [hi,hm,ha,Nat.zero_le tail.length]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ) (path : List Bool) :
    (run primitive W path).2≤64*(path.length+1)*(W+primitive (8+2*(path.length+1))) :=
  fold_work primitive hMono W path.length path 0 0 (by simp) (by decide)

theorem arithmetic_work (path : List Bool) : (run (fun _ => 1) 1 path).2≤128*(path.length+1) := by
  have h := work (fun _ => 1) (by intro a b h; rfl) 1 path
  nlinarith only [h]

end Blotto.GeneralPaperQuantilePathPrice
