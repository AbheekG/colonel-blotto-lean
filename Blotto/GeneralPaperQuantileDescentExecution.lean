import Blotto.GeneralPaperQuantileStepPrice
import Blotto.GeneralPaperQuantileWork

/-! One single-path recursive execution uses the retained step records.
The right mass is evaluated only on the right branch. Virtual child cursors,
ancestor/height control, path cons, visits and native work metadata are all
priced. A model flag selects bit or separate unit component implementations.
-/
namespace Blotto.GeneralPaperQuantileDescentExecution
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperQuantileDescent GeneralPaperQuantileStepPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def step (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits j ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number) : Step × ℕ :=
  if bits then GeneralPaperQuantileStepPrice.run primitive W c digits j ancestor node total storedMass storedPrefix
  else GeneralPaperQuantileStepPrice.arithmetic c digits j ancestor node total storedMass storedPrefix

def right (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (storedMass : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  if bits then GeneralPaperQuantileChildPrice.run true primitive W c ancestor node storedMass
  else GeneralPaperQuantileChildPrice.arithmetic true c ancestor node storedMass

def metadata (primitive : ℕ → ℕ) (child : Result) (s : Step) (rightWork : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) child.work s.left.work+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (child.work+s.left.work) rightWork+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (child.work+s.left.work+rightWork) s.through.work+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (child.work+s.left.work+rightWork+s.through.work) s.comparison.work+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (child.work+s.left.work+rightWork+s.through.work+s.comparison.work) 24+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) child.visits 1

def finish (primitive : ℕ → ℕ) (W : ℕ) (bit : Bool) (child : Result) (s : Step) (rightWork : ℕ) : Result × ℕ :=
  (⟨bit::child.path,child.work+s.left.work+rightWork+s.through.work+s.comparison.work+24,child.visits+1⟩,
    metadata primitive child s rightWork+128*W)

def advance (primitive : ℕ → ℕ) (W height ancestor level : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare primitive (height+1) 0+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) ancestor level+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) (height+1) 1+
  primitive (1+binaryWordWidth height)+128*W

def run (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits j : ℕ) (total : Number) : (height : ℕ) → Node height → ℕ → Number → Number → Result × ℕ
  | 0,_,_,_,_ => (⟨[],8,1⟩,64*W+GeneralPaperIntegerWordPrice.compare primitive 0 0)
  | height+1,node,ancestor,storedMass,storedPrefix =>
    let s := step bits primitive W c digits j ancestor node total storedMass storedPrefix
    let next := ancestor+offset node
    let common := s.2+advance primitive W height ancestor (offset node)
    if s.1.comparison.answer then
      let child := run bits primitive W c digits j total height (leftChild node) next s.1.left.number storedPrefix
      let result := finish primitive W false child.1 s.1 0
      (result.1,common+child.2+result.2)
    else
      let r := right bits primitive W c ancestor node storedMass
      let child := run bits primitive W c digits j total height (rightChild node) next r.1.number s.1.through.number
      let result := finish primitive W true child.1 s.1 r.1.work
      (result.1,common+r.2+child.2+result.2)

end Blotto.GeneralPaperQuantileDescentExecution
