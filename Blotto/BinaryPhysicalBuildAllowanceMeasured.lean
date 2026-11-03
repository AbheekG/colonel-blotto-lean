import Blotto.BinaryBuildAllowanceArithmeticMeasured
import Blotto.BinaryHeapAllocationMeasured

/-! Actual carry counting, schoolbook products, full addition and node-word
construction produce the Boolean builder allowance, its old trace and its old
work charge together. No separate calculator/work replay occurs. Native trace
observer evaluation, bit-address ownership and allocator/GC remain separate. -/
namespace Blotto.BinaryPhysicalBuildAllowanceMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPhysicalBuildAllowance
open BinaryBuildAllowanceArithmeticMeasured
set_option autoImplicit false

def tree (nodes tape : List Bool) : (List Bool × Trace) × ℕ :=
  let counted := BinaryHeapAllocationMeasured.count tape [true]
  let square := multiply counted.1.1 counted.1.1
  let scaled := multiply hundred square.1.1
  let allocation := add scaled.1.1 eight
  let product := multiply nodes allocation.1.1
  ((product.1.1,wrapList 11 64 4 [counted.1.2,square.1.2,scaled.1.2,allocation.1.2,product.1.2]),
    counted.2.work+square.2+scaled.2+allocation.2+product.2+16)

theorem tree_erases (nodes tape : List Bool) : (tree nodes tape).1 = BinaryPhysicalBuildAllowanceLifetime.treeWithTrace nodes tape := by
  simp only [tree,BinaryPhysicalBuildAllowanceLifetime.treeWithTrace,BinaryHeapAllocationMeasured.count_erases,
    multiply_erases,add_erases]

theorem tree_data (nodes tape : List Bool) : (tree nodes tape).1.1 = (treeWithWork nodes tape).1 := by
  rw [tree_erases,BinaryPhysicalBuildAllowanceLifetime.treeWithTrace_erases,treeWithWork_erases]

theorem tree_work (nodes tape : List Bool) : (tree nodes tape).2 = (treeWithWork nodes tape).2 := by
  simp only [tree,treeWithWork,BinaryHeapAllocationMeasured.count_charge,BinaryHeapAllocationMeasured.count_data,
    multiply_work,add_work,multiply_data,add_data]

def calculate (ruler first second : List Bool) : (List Bool × Trace) × ℕ :=
  let nodes := BinaryBuildAllowanceArithmeticMeasured.nodes ruler
  let a := tree nodes.1.1 first
  let b := tree nodes.1.1 second
  let combined := add a.1.1 b.1.1
  ((combined.1.1,wrap 64 4 [nodes.1.2,a.1.2,b.1.2,combined.1.2]),nodes.2+a.2+b.2+combined.2+8)

theorem calculate_erases (ruler first second : List Bool) :
    (calculate ruler first second).1 = BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace ruler first second := by
  simp only [calculate,BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace,nodes_erases,tree_erases,add_erases]

theorem calculate_work (ruler first second : List Bool) :
    (calculate ruler first second).2 = (calculateWithWork ruler first second).2 := by
  simp only [calculate,calculateWithWork,nodes_work,nodes_data,tree_work,tree_data,add_work]

theorem calculate_value (ruler first second : List Bool) :
    BinaryBigEndian.littleValue (calculate ruler first second).1.1 =
      BinaryPRGWordStoreHeapMachine.nodes ruler.length*(BinaryPRGWordStoreHeapMachine.allocationBound first.length+8)+
        BinaryPRGWordStoreHeapMachine.nodes ruler.length*(BinaryPRGWordStoreHeapMachine.allocationBound second.length+8) := by
  rw [calculate_erases,BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace_erases,← calculateWithWork_erases]
  exact calculateWithWork_value ruler first second

theorem calculate_bound (ruler first second : List Bool) :
    (calculate ruler first second).2 ≤ 30000*(ruler.length+first.length+second.length+9)^2 := by
  rw [calculate_work]
  exact calculateWithWork_bound ruler first second

theorem calculate_usage (ruler first second : List Bool) :
    usage (calculate ruler first second).1.2 ≤ 300000*(ruler.length+first.length+second.length+9)^2 := by
  rw [calculate_erases]
  exact BinaryPhysicalBuildAllowanceLifetime.calculateWithTrace_usage ruler first second

theorem all_prefix (ruler first second : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (calculate ruler first second).1.2 steps ≤
      borrowed+300000*(ruler.length+first.length+second.length+9)^2 ∧
    framePeak ((calculate ruler first second).1.2.take steps) ≤ 300000*(ruler.length+first.length+second.length+9)^2 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (calculate_usage ruler first second) _ steps

end Blotto.BinaryPhysicalBuildAllowanceMeasured
