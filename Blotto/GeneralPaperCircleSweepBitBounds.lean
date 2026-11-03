import Blotto.GeneralPaperCircleSweepBits

/-! Erased uniform magnitude bounds for every operand written by a
valid retained-circle sweep. The bound depends on R and W, not the arc
count or a supplied runtime height/capacity. -/
namespace Blotto.GeneralPaperCircleSweepBitBounds
open GeneralPaperCircleSweepBits
set_option autoImplicit false
set_option maxHeartbeats 3500000

def magnitude (R W : ℕ) : ℕ := 64*(R*W+R+W+1)
def width (R W : ℕ) : ℕ := 1+binaryWordWidth (magnitude R W)

theorem next_bound (R W a next : ℕ) (ha : a<2*R) (hn : next=(a+1)*(2*W)) : next≤4*(R*W) := by
  have hh := Nat.mul_le_mul_right (2*W) (show a+1≤2*R by omega)
  rw [hn]
  nlinarith only [hh]

theorem advance_price (price : ℕ → ℕ) (hMono : Monotone price) (A R W t offset length a next : ℕ)
    (ht : t<R*W) (hArc : offset+length≤R*W) (ha : a<2*R) (hn : next=(a+1)*(2*W)) :
    (GeneralPaperCircleBinAdvancePrice.run price A (2*W) (2*(t+offset)+1) (2*R) a next).2≤
      ((GeneralPaperCircleBinAdvancePrice.run price A (2*W) (2*(t+offset)+1) (2*R) a next).1.advances+1)*
        (128*A+32*price (width R W)) := by
  have hNext := next_bound R W a next ha hn
  apply GeneralPaperCircleBinAdvancePrice.bounded_work price hMono
  all_goals dsimp only [width,magnitude]
  · omega
  · omega
  · nlinarith only [hNext,Nat.zero_le (R*W),Nat.zero_le R,Nat.zero_le W]
  · omega
  · omega
  · omega

theorem fixed_price (price : ℕ → ℕ) (hMono : Monotone price) (R W t offset length : ℕ)
    (advanced : GeneralPaperCircleBinAdvance.Result) (later : State)
    (ht : t<R*W) (hArc : offset+length≤R*W) (hAdv : advanced.advances≤2*R)
    (hLater : later.advances<2*R) (hBin : later.bin<2*R) (hNext : later.next=(later.bin+1)*(2*W)) :
    fixedCost price R W t offset length advanced later≤25*price (width R W) := by
  let M := magnitude R W
  let P := price (width R W)
  have hN := next_bound R W later.bin later.next hBin hNext
  have hM : 2≤M := by dsimp only [M,magnitude];omega
  have hR : R≤M := by dsimp only [M,magnitude];omega
  have hW : W≤M := by dsimp only [M,magnitude];omega
  have hRW : R*W≤M := by dsimp only [M,magnitude];omega
  have hT : t≤M := by omega
  have hO : offset≤M := by omega
  have hL : length≤M := by omega
  have hU : t+offset≤M := by dsimp only [M,magnitude];omega
  have hV : t+offset+length≤M := by dsimp only [M,magnitude];omega
  have hLeft : 2*(t+offset)+1≤M := by dsimp only [M,magnitude];omega
  have hRight : 2*(t+offset+length)+1≤M := by dsimp only [M,magnitude];omega
  have hTwoW : 2*W≤M := by dsimp only [M,magnitude];omega
  have hTwoR : 2*R≤M := by dsimp only [M,magnitude];omega
  have hSum : advanced.advances+later.advances≤M := by dsimp only [M,magnitude];omega
  have hb := GeneralPaperNaturalPrimitivePrice.binary_le price hMono
  have h1 := hb (fun a b => a+b) t offset M hT hO hU
  have h2 := hb (fun a b => a*b) 2 (t+offset) M hM hU (by omega)
  have h3 := hb (fun a b => a+b) (2*(t+offset)) 1 M (by omega) (by omega) hLeft
  have h4 := hb (fun a b => a+b) (t+offset) length M hU hL hV
  have h5 := hb (fun a b => a*b) 2 (t+offset+length) M hM hV (by omega)
  have h6 := hb (fun a b => a+b) (2*(t+offset+length)) 1 M (by omega) (by omega) hRight
  have h7 := hb (fun a b => a*b) 2 W M hM hW hTwoW
  have h8 := hb (fun a b => a*b) 2 R M hM hR hTwoR
  have h9 := hb (fun a b => a*b) R W M hR hW hRW
  have h10 := hb (fun a b => a+b) advanced.advances later.advances M (by omega) (by omega) hSum
  have hCopy (x : ℕ) (hx : x≤M) : price (GeneralPaperNaturalPrimitivePrice.word x)≤P :=
    hMono (Nat.add_le_add_left (binaryWordWidth_mono hx) 1)
  have hc1 := hCopy offset hO
  have hc2 := hCopy length hL
  have hc3 := hCopy later.bin (by omega)
  have hc4 := hCopy later.next (by dsimp only [M,magnitude];omega)
  have hc5 := hCopy (advanced.advances+later.advances) hSum
  change _≤2*P at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  unfold fixedCost
  dsimp only
  omega

end Blotto.GeneralPaperCircleSweepBitBounds
