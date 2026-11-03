import Blotto.PlayerSpecificOrderedFourDrawSourceCost
import Blotto.PlayerSpecificAlgebraicSortTriple

/-! Three executed comparisons form the stable sorting permutation. The
returned rows and permutation words are copied in the measured frame. -/
namespace Blotto.PlayerSpecificSortTripleExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def compare (root : Candidate) (a : FixedArrayTable 3 Data) (i j : Fin 3) :
    Equiv.Perm (Fin 3) × ℕ :=
  let model := RationalCostModel.schoolbook
  let c := PlayerSpecificAlgebraicComparisonExecution.run model root (a.read i) (a.read j)
  (if c.1 then Equiv.refl _ else Equiv.swap i j, c.2 + price model [.control 1])

theorem compare_value (root : Candidate) (a : FixedArrayTable 3 Data) (i j : Fin 3) :
    (compare root a i j).1 =
      PlayerSpecificAlgebraicSortTriple.compare RationalCostModel.schoolbook root a i j := by
  simp only [compare, PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicSortTriple.compare]

def frame (root : Candidate) (input output : FixedArrayTable 3 Data)
    (p : Equiv.Perm (Fin 3)) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root input output ++
    (List.ofFn (fun j : Fin 3 => Event.control (p j).val))

def run (root : Candidate) (a : FixedArrayTable 3 Data) :
    PlayerSpecificAlgebraicSortTriple.Prepared × ℕ :=
  let model := RationalCostModel.schoolbook
  let first := compare root a 0 1
  let M := PlayerSpecificAlgebraicPermutation.permute first.1 a
  let second := compare root M 1 2
  let N := PlayerSpecificAlgebraicPermutation.permute second.1 M
  let third := compare root N 0 1
  let p := (third.1.trans second.1).trans first.1
  let result : PlayerSpecificAlgebraicSortTriple.Prepared :=
    ⟨PlayerSpecificAlgebraicPermutation.permute p a,p⟩
  (result, first.2 + second.2 + third.2 + price model (frame root a result.lengths p) +
    price model [.control 1])

theorem value (root : Candidate) (a : FixedArrayTable 3 Data) :
    (run root a).1 = PlayerSpecificAlgebraicSortTriple.prepare RationalCostModel.schoolbook root a := by
  simp only [run, compare_value, PlayerSpecificAlgebraicSortTriple.prepare,
    PlayerSpecificAlgebraicSortTriple.permutation]

end Blotto.PlayerSpecificSortTripleExecution
