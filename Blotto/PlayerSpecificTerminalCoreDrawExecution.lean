import Blotto.PlayerSpecificComplementaryDrawSourceCost
import Blotto.PlayerSpecificThreeDrawSourceCost
import Blotto.PlayerSpecificFourSpecDrawSourceCost
import Blotto.PlayerSpecificAlgebraicTerminalCoreDraw

/-! The actual four-case terminal core executes only the selected
two- or three-group continuation, retaining input/output rows once. -/
namespace Blotto.PlayerSpecificTerminalCoreDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a : Input) : FixedArrayTable 6 Data :=
  FixedArrayTable.ofFn ![a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,
    a.fractional.map Prod.fst |>.getD [],a.fractional.map Prod.snd |>.getD []]

def frame (root : PlayerSpecificAlgebraicCandidates.Candidate) (a : Input)
    (result : FixedArrayTable 4 Data) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (environment a) result ++
    [Event.control a.count,Event.control (if a.fractional.isSome then 1 else 0)]

def selected (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FixedArrayTable 4 Data × ℕ :=
  let model := RationalCostModel.schoolbook
  if a.count=2 then
    match a.fractional with
    | none =>
      let headBits := PlayerSpecificBitSliceExecution.run model
        (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) 0 K
        (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K) bits
      let drawn := PlayerSpecificComplementaryDrawExecution.run r.root a.budget K headBits.1
      (drawn.1,headBits.2+drawn.2+price model [.control 1])
    | some (ell,probability) =>
      let headBits := PlayerSpecificBitSliceExecution.run model
        (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) 0 (8*H+K)
        (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits
      let drawn := PlayerSpecificThreeDrawExecution.run model r.root (mixedThree a ell probability) H K headBits.1
      (PlayerSpecificAlgebraicTerminalEmbedding.mixed drawn.1,
        headBits.2+drawn.2+price model [.control 1])
  else
    match a.fractional with
    | none =>
      let one := PlayerSpecificFieldCombinationContract.constant r.root.polynomial 1
      let headBits := PlayerSpecificBitSliceExecution.run model
        (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) 0 (8*H+K)
        (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits
      let input : PlayerSpecificAlgebraicThreeInput.Input :=
        ⟨a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,one.1⟩
      let drawn := PlayerSpecificThreeDrawExecution.run model r.root input H K headBits.1
      (PlayerSpecificAlgebraicTerminalEmbedding.uniform drawn.1,
        price model one.2+headBits.2+drawn.2+price model [.control 1])
    | some (ell,probability) =>
      let drawn := PlayerSpecificFourSpecDrawExecution.run r (mixedFour a ell probability) H K bits
      (drawn.1,drawn.2+price model [.control 1])

theorem head_bits (H K n : ℕ) (hn : n ≤ PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook
      (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) 0 n
      (by simpa only [Nat.zero_add] using hn) bits).1 =
      PlayerSpecificAlgebraicFourSmallDraw.takeBits hn bits := by
  rw [PlayerSpecificBitSliceExecution.value]
  funext j
  simp only [PlayerSpecificBitSliceExecution.address,
    PlayerSpecificAlgebraicFourSmallDraw.takeBits,Nat.zero_add]

theorem selected_value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (selected r a H K bits).1 = PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits := by
  by_cases hc : a.count=2
  · simp only [selected,PlayerSpecificAlgebraicTerminalCoreDraw.draw,hc,ite_true]
    cases hf : a.fractional with
    | none =>
      simp only [PlayerSpecificComplementaryDrawExecution.value]
      exact head_bits H K K (PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K) bits ▸ rfl
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      simp only [PlayerSpecificThreeDrawExecution.value]
      exact head_bits H K (8*H+K) (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits ▸ rfl
  · simp only [selected,PlayerSpecificAlgebraicTerminalCoreDraw.draw,hc,ite_false]
    cases hf : a.fractional with
    | none =>
      simp only [PlayerSpecificFieldCombinationContract.constant_value,
        PlayerSpecificThreeDrawExecution.value,uniformThree]
      exact head_bits H K (8*H+K) (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits ▸ rfl
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      exact PlayerSpecificFourSpecDrawExecution.value r (mixedFour a ell probability) H K bits

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FixedArrayTable 4 Data × ℕ :=
  let model := RationalCostModel.schoolbook
  let drawn := selected r a H K bits
  (drawn.1,drawn.2+price model (frame r.root a drawn.1)+price model [.control 1])

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (run r a H K bits).1 = PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits :=
  selected_value r a H K bits

end Blotto.PlayerSpecificTerminalCoreDrawExecution
