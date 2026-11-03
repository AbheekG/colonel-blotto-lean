import Blotto.GeneralPaperCircleSelectBits
import Blotto.GeneralPaperCircleBinAdvancePrice

/-! Operand-priced sweep over the actual retained arc list. Its cursor
and advance counter are carried across arcs. The unused arithmetic work
annotation is absent from bit data; all selected indices/cursors agree. -/
namespace Blotto.GeneralPaperCircleSweepBits
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

structure State where
  indices : List ℕ
  bin : ℕ
  next : ℕ
  advances : ℕ

def observe (x : GeneralPaperCircleCursorSweep.Result) : State := ⟨x.indices,x.bin,x.next,x.advances⟩

def fixedCost (price : ℕ → ℕ) (R W t offset length : ℕ)
    (advanced : GeneralPaperCircleBinAdvance.Result) (later : State) : ℕ :=
  let u := t+offset
  let v := u+length
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) t offset+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 u+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*u) 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) u length+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 v+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*v) 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 W+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 R+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) R W+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) advanced.advances later.advances+
    price (GeneralPaperNaturalPrimitivePrice.word offset)+price (GeneralPaperNaturalPrimitivePrice.word length)+
    price (GeneralPaperNaturalPrimitivePrice.word later.bin)+price (GeneralPaperNaturalPrimitivePrice.word later.next)+
    price (GeneralPaperNaturalPrimitivePrice.word (advanced.advances+later.advances))

def run (price : ℕ → ℕ) (A R W t : ℕ) : List (ℕ×ℕ) → ℕ → ℕ → State×ℕ
  | [],a,next => (⟨[],a,next,0⟩,32*A+price (GeneralPaperNaturalPrimitivePrice.word a)+
      price (GeneralPaperNaturalPrimitivePrice.word next)+price (GeneralPaperNaturalPrimitivePrice.word 0))
  | (offset,length)::tail,a,next =>
    let u := t+offset
    let left := 2*u+1
    let right := 2*(u+length)+1
    let advanced := GeneralPaperCircleBinAdvancePrice.run price A (2*W) left (2*R) a next
    let chosen := GeneralPaperCircleSelectBits.run price A R (R*W) left right advanced.1.bin
    let later := run price A R W t tail advanced.1.bin advanced.1.next
    (⟨chosen.1::later.1.indices,later.1.bin,later.1.next,advanced.1.advances+later.1.advances⟩,
      advanced.2+chosen.2+later.2+fixedCost price R W t offset length advanced.1 later.1+64*A)

theorem data (price : ℕ → ℕ) (A R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) :
    (run price A R W t arcs a next).1=observe (GeneralPaperCircleCursorSweep.run R W t arcs a next) := by
  induction arcs generalizing a next with
  | nil => rfl
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    dsimp only [run]
    rw [GeneralPaperCircleBinAdvancePrice.data,GeneralPaperCircleSelectBits.data,ih]
    rfl

theorem indices_length (price : ℕ → ℕ) (A R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) :
    (run price A R W t arcs a next).1.indices.length=arcs.length := by
  rw [data]
  exact GeneralPaperCircleCursorSweep.indices_length R W t arcs a next

end Blotto.GeneralPaperCircleSweepBits
