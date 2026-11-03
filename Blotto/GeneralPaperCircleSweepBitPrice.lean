import Blotto.GeneralPaperCircleSweepBitInvariant

/-! Full reached-operation bit bound for the native ordered sweep.
Bin advances telescope across arcs; the numeric fuel is not a work bound.
The arc order/range premises are discharged by retained metadata builders. -/
namespace Blotto.GeneralPaperCircleSweepBitPrice
open GeneralPaperCircleSweepBits GeneralPaperCircleSweepBitBounds
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def unitPrice (price : ℕ → ℕ) (A R W : ℕ) : ℕ := 512*A+256*price (width R W)

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (A R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ)) (a next : ℕ) (ha : a<2*R) (hn : next=(a+1)*(2*W))
    (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W)
    (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1))
    (hLower : ∀ arc∈arcs,a*(2*W)<2*(t+arc.1)+1) :
    (run price A R W t arcs a next).2≤
      ((run price A R W t arcs a next).1.advances+arcs.length+1)*unitPrice price A R W := by
  let M := magnitude R W
  let P := price (width R W)
  have hCopy (x : ℕ) (hx : x≤M) : price (GeneralPaperNaturalPrimitivePrice.word x)≤P :=
    hMono (Nat.add_le_add_left (binaryWordWidth_mono hx) 1)
  induction arcs generalizing a next with
  | nil =>
    have hnCap := next_bound R W a next ha hn
    have h1 := hCopy a (by dsimp only [M,magnitude];omega)
    have h2 := hCopy next (by dsimp only [M,magnitude];omega)
    have h0 := hCopy 0 (Nat.zero_le _)
    simp only [run,List.length_nil,Nat.zero_add,Nat.one_mul,unitPrice]
    change 32*A+price (GeneralPaperNaturalPrimitivePrice.word a)+price (GeneralPaperNaturalPrimitivePrice.word next)+
      price (GeneralPaperNaturalPrimitivePrice.word 0)≤512*A+256*P
    omega
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    have hArc := hRanges (offset,length) List.mem_cons_self
    let advanced := GeneralPaperCircleBinAdvancePrice.run price A (2*W) (2*(t+offset)+1) (2*R) a next
    let chosen := GeneralPaperCircleSelectBits.run price A R (R*W) (2*(t+offset)+1) (2*(t+offset+length)+1) advanced.1.bin
    let later := run price A R W t tail advanced.1.bin advanced.1.next
    have hAdv := GeneralPaperCircleSweepBitInvariant.advanced price A R W t offset hR hW a next (by omega) hn
      (hLower (offset,length) List.mem_cons_self)
    change advanced.1.bin<2*R ∧ advanced.1.next=(advanced.1.bin+1)*(2*W) ∧
      advanced.1.bin*(2*W)<2*(t+offset)+1 ∧ advanced.1.advances≤2*R at hAdv
    have hTailRanges : ∀ item∈tail,item.1+item.2≤R*W := fun item hm => hRanges item (List.mem_cons_of_mem _ hm)
    have hPair := List.pairwise_cons.mp hOrder
    have hTailLower : ∀ item∈tail,advanced.1.bin*(2*W)<2*(t+item.1)+1 := by
      intro item hm
      have hOff := hPair.1 item hm
      omega
    have hi := ih advanced.1.bin advanced.1.next hAdv.1 hAdv.2.1 hTailRanges hPair.2 hTailLower
    have hLater := GeneralPaperCircleSweepBitInvariant.state price A R W t hR hW ht tail advanced.1.bin advanced.1.next
      hAdv.1 hAdv.2.1 hTailRanges hPair.2 hTailLower
    change later.1.bin<2*R ∧ later.1.next=(later.1.bin+1)*(2*W) ∧ later.1.advances<2*R at hLater
    have hb := advance_price price hMono A R W t offset length a next ht hArc ha hn
    have hc := GeneralPaperCircleSelectBits.work price hMono A R (R*W) (2*(t+offset)+1)
      (2*(t+offset+length)+1) advanced.1.bin M
      (by dsimp only [M,magnitude];omega) (by dsimp only [M,magnitude];omega)
      (by dsimp only [M,magnitude];omega) (by dsimp only [M,magnitude];omega)
      (by dsimp only [M,magnitude];omega) (by dsimp only [M,magnitude];omega)
    have hf := fixed_price price hMono R W t offset length advanced.1 later.1 ht hArc hAdv.2.2.2
      hLater.2.2 hLater.1 hLater.2.1
    change advanced.2≤(advanced.1.advances+1)*(128*A+32*P) at hb
    change chosen.2≤48*A+8*P at hc
    change fixedCost price R W t offset length advanced.1 later.1≤25*P at hf
    change later.2≤(later.1.advances+tail.length+1)*(512*A+256*P) at hi
    change advanced.2+chosen.2+later.2+fixedCost price R W t offset length advanced.1 later.1+64*A≤
      (advanced.1.advances+later.1.advances+(tail.length+1)+1)*(512*A+256*P)
    nlinarith only [hb,hc,hf,hi,Nat.zero_le (advanced.1.advances*A),Nat.zero_le (advanced.1.advances*P)]

theorem initial_work (price : ℕ → ℕ) (hMono : Monotone price) (A R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ)) (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W)
    (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1)) :
    (run price A R W t arcs 0 (2*W)).2≤(2*R+arcs.length+1)*unitPrice price A R W := by
  have hlo : ∀ arc∈arcs,0*(2*W)<2*(t+arc.1)+1 := by intro arc _;omega
  have hw := work price hMono A R W t hR hW ht arcs 0 (2*W) (by omega) (by omega) hRanges hOrder hlo
  have hi := GeneralPaperCircleSweepBitInvariant.state price A R W t hR hW ht arcs 0 (2*W) (by omega) (by omega)
    hRanges hOrder hlo
  exact hw.trans (Nat.mul_le_mul_right _ (by omega))

end Blotto.GeneralPaperCircleSweepBitPrice
