import Blotto.GeneralPaperQuantilePath

/-! One actual descent through cached intervals. At a uniform interval the
child cursors are virtual: only an encoded halving is performed, and the
retained tree is never expanded. A final linear path fold returns its code.
-/
namespace Blotto.GeneralPaperQuantileDescent
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  path : List Bool
  work : ℕ
  visits : ℕ

def leftMass (prepared : Prepared) (ancestor : ℕ) {height : ℕ}
    (node : Node (height+1)) (storedMass : Number) : GeneralPaperDyadicMultiply.Result :=
  match node with
  | .uniform _ _ => ⟨GeneralPaperDyadicShift.shift storedMass (-1),8⟩
  | .branch level _ left _ => fresh prepared (ancestor+level) left

def rightMass (prepared : Prepared) (ancestor : ℕ) {height : ℕ}
    (node : Node (height+1)) (storedMass : Number) : GeneralPaperDyadicMultiply.Result :=
  match node with
  | .uniform _ _ => ⟨GeneralPaperDyadicShift.shift storedMass (-1),8⟩
  | .branch level _ _ right => fresh prepared (ancestor+level) right

def run (prepared : Prepared) (width j s : ℕ) (storedTotal : Number) :
    (height : ℕ) → Node height → ℕ → Number → Number → Result
  | 0,_,_,_,_ => ⟨[],8,1⟩
  | height+1,node,ancestor,storedMass,storedPrefix =>
    let left := leftMass prepared ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits storedPrefix left.number
    let comparison := GeneralPaperDyadicCompare.scaledLE width j storedTotal s through.number
    if comparison.answer then
      let child := run prepared width j s storedTotal height (leftChild node) (ancestor+offset node) left.number storedPrefix
      ⟨false::child.path,child.work+left.work+through.work+comparison.work+24,child.visits+1⟩
    else
      let right := rightMass prepared ancestor node storedMass
      let child := run prepared width j s storedTotal height (rightChild node) (ancestor+offset node) right.number through.number
      ⟨true::child.path,child.work+left.work+right.work+through.work+comparison.work+24,child.visits+1⟩

def code (result : Result) : ℕ := GeneralPaperQuantilePath.encode result.path

theorem path_length (prepared : Prepared) (width j s : ℕ) (storedTotal : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    (run prepared width j s storedTotal height node ancestor storedMass storedPrefix).path.length=height := by
  induction height generalizing ancestor storedMass storedPrefix with
  | zero => rfl
  | succ height ih =>
    rw [run]
    split <;> dsimp only <;> rw [List.length_cons,ih]

theorem code_bound (prepared : Prepared) (width j s : ℕ) (storedTotal : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    code (run prepared width j s storedTotal height node ancestor storedMass storedPrefix)<2^height := by
  rw [code,GeneralPaperQuantilePath.encode_index]
  have he := GeneralPaperQuantilePath.index_bound
    (run prepared width j s storedTotal height node ancestor storedMass storedPrefix).path
  simpa only [path_length] using he

theorem visits (prepared : Prepared) (width j s : ℕ) (storedTotal : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    (run prepared width j s storedTotal height node ancestor storedMass storedPrefix).visits=height+1 := by
  induction height generalizing ancestor storedMass storedPrefix with
  | zero => rfl
  | succ height ih =>
    rw [run]
    split <;> dsimp only <;> rw [ih]

end Blotto.GeneralPaperQuantileDescent
