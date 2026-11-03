import Blotto.PlayerSpecificResourceSourcePolynomial

/-! Actual fixed fair-packet block construction with measured offset
arithmetic and one materialization of every reserved bit. The resulting
functions equal the native block views on every packet, including H=0. -/
namespace Blotto.PlayerSpecificResourceBlockExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def address (fuel H : ℕ) (i : Fin fuel) (j : Fin H) : Fin (fuel*H) :=
  ⟨i.val*H+j.val,by
    have hi:=Nat.mul_le_mul_right H (Nat.succ_le_of_lt i.isLt)
    have hj:=j.isLt
    nlinarith⟩

def read (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) (j : Fin H) : Bool×ℕ :=
  let base:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) i.val H
  let offset:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) base.1 j.val
  let index:Fin (fuel*H):=⟨offset.1,by
    change i.val*H+j.val<fuel*H
    have hi:=Nat.mul_le_mul_right H (Nat.succ_le_of_lt i.isLt)
    have hj:=j.isLt
    nlinarith⟩
  (bits index,base.2+offset.2+price model (PlayerSpecificAlgebraicCallerFrame.run [] [fuel,H,i.val,j.val,offset.1])+2)

theorem read_value (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) (j : Fin H) :
    (read model fuel H bits i j).1=bits (address fuel H i j) := rfl

def block (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) : (Fin H → Bool)×ℕ :=
  let data:=FixedArrayTable.ofFn (read model fuel H bits i)
  (fun j => (data.read j).1,(∑ j,(data.read j).2)+2*H+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] ([fuel,H,i.val]++List.range H)))

theorem block_value (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) :
    (block model fuel H bits i).1=fun j => bits (address fuel H i j) := by
  funext j
  simp only [block,FixedArrayTable.read_ofFn,read_value]

def blocks (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) : List (Fin H → Bool)×ℕ :=
  let count:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) fuel H
  let prepared:=List.ofFn (block model fuel H bits)
  (prepared.map Prod.fst,(prepared.map Prod.snd).sum+count.2+2*fuel+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] ([fuel,H,count.1]++List.range fuel)))

theorem blocks_value (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) :
    (blocks model fuel H bits).1=PlayerSpecificFiniteResourceLoop.blocks fuel H bits := by
  simp only [blocks,List.map_ofFn,PlayerSpecificFiniteResourceLoop.blocks]
  apply congrArg List.ofFn
  funext i
  change (block model fuel H bits i).1=fun j => bits ⟨i.val*H+j.val,_⟩
  rw [block_value]
  rfl

theorem blocks_length (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) :
    (blocks model fuel H bits).1.length=fuel := by
  rw [blocks_value,PlayerSpecificFiniteResourceLoop.blocks_length]

end Blotto.PlayerSpecificResourceBlockExecution
