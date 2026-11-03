import Blotto.PlayerSpecificSegmentInterpolationSourceCost

/-! Actual finite bit slices cache each addressed bit once. Every
offset addition, Boolean copy, finite array and returned view is priced. -/
namespace Blotto.PlayerSpecificBitSliceExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def address (M offset K : ℕ) (h : offset+K≤M) (j : Fin K) : Fin M := ⟨offset+j.val,by have hj:=j.isLt; omega⟩

def read (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) (j : Fin K) : Bool×ℕ :=
  let computed:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) offset j.val
  let index:Fin M:=⟨computed.1,by change offset+j.val<M; have hj:=j.isLt; omega⟩
  (bits index,computed.2+price model (PlayerSpecificAlgebraicCallerFrame.run [] [M,K,offset,j.val,computed.1])+2)

def run (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) : (Fin K → Bool)×ℕ :=
  let cached:=FixedArrayTable.ofFn (read model M offset K h bits)
  (fun j => (cached.read j).1,(∑ j : Fin K,(cached.read j).2)+2*K+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] ([M,K,offset]++List.range K)))

theorem read_value (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) (j : Fin K) :
    (read model M offset K h bits j).1=bits (address M offset K h j) := rfl

theorem value (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) :
    (run model M offset K h bits).1=fun j => bits (address M offset K h j) := by
  funext j
  simp only [run,FixedArrayTable.read_ofFn,read_value]

theorem first_value (model : RationalCostModel) (R K : ℕ) (bits : Fin (R+K) → Bool) :
    (run model (R+K) 0 R (by omega) bits).1=firstBitBlock R K bits := by
  rw [value]
  funext j
  unfold address firstBitBlock
  simp only [Nat.zero_add]
  rfl

theorem second_value (model : RationalCostModel) (R K : ℕ) (bits : Fin (R+K) → Bool) :
    (run model (R+K) R K (Nat.le_refl _) bits).1=secondBitBlock R K bits := by
  rw [value]
  rfl

end Blotto.PlayerSpecificBitSliceExecution
