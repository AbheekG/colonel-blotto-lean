import Blotto.GeneralPaperWordLengthLifetime

/-! Each actual address sum/product reserves operand/result words, local
primitive scratch and its price fields. The full reserve keeps all source
operands/steps and partial price accumulations at once, including both
stored-word scans. It adds no executed metadata or width census. -/
namespace Blotto.GeneralPaperAddressConstructionLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEqualAddressConstruction (price)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def scalarFoot (model : RationalCostModel) (A a b out : ℕ) : ℕ :=
  natBits a + natBits b + natBits out + price model A a b out +
    fields A [price model A a b out, 16 * A, 16] + 64 * A

theorem scalar_bound (model : RationalCostModel) (A a b out : ℕ) :
    scalarFoot model A a b out ≤ 32 * price model A a b out := by
  let F := price model A a b out
  have hWords : natBits a + natBits b + natBits out + 16 * A + 16 ≤ F := by
    dsimp only [F, price, GeneralPaperNaturalScalarStep.word, natBits]
    omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A F [F, 16 * A, 16] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 3 * (natBits F + A) + 32 * A at hFields
  have hCounter := GeneralPaperNaturalScalarLifetime.counter_word F
  change natBits a + natBits b + natBits out + F + fields A [F, 16 * A, 16] + 64 * A ≤ 32 * F
  omega

def footprint (model : RationalCostModel) (A n m k b : ℕ) : ℕ :=
  let nw := GeneralPaperStoredWordLength.run A n
  let s0 := b + nw.1
  let s1 := s0 + k
  let size := s1 + 10
  let draw := 67108864 * size
  let c0 := n + m
  let c1 := c0 + k
  let count := c1 + 69
  let stride := draw + 1
  let pool := count * stride
  let target := pool + 1
  let address := GeneralPaperStoredWordLength.run A target
  let p0 := price model A b nw.1 s0
  let p1 := price model A s0 k s1
  let p2 := price model A s1 10 size
  let p3 := price model A 67108864 size draw
  let p4 := price model A n m c0
  let p5 := price model A c0 k c1
  let p6 := price model A c1 69 count
  let p7 := price model A draw 1 stride
  let p8 := price model A count stride pool
  let p9 := price model A pool 1 target
  let F := (GeneralPaperEqualAddressConstruction.run model A n m k b).2
  GeneralPaperWordLengthLifetime.footprint A n +
    scalarFoot model A b nw.1 s0 +
    scalarFoot model A s0 k s1 +
    scalarFoot model A s1 10 size +
    scalarFoot model A 67108864 size draw +
    scalarFoot model A n m c0 +
    scalarFoot model A c0 k c1 +
    scalarFoot model A c1 69 count +
    scalarFoot model A draw 1 stride +
    scalarFoot model A count stride pool +
    scalarFoot model A pool 1 target +
    GeneralPaperWordLengthLifetime.footprint A target + fields A [nw.2, nw.2 + p0, nw.2 + p0 + p1, nw.2 + p0 + p1 + p2, nw.2 + p0 + p1 + p2 + p3, nw.2 + p0 + p1 + p2 + p3 + p4, nw.2 + p0 + p1 + p2 + p3 + p4 + p5, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + address.2, F] + 256 * A

theorem bounded (model : RationalCostModel) (A n m k b : ℕ) :
    footprint model A n m k b ≤ 1024 * (GeneralPaperEqualAddressConstruction.run model A n m k b).2 := by
  let nw := GeneralPaperStoredWordLength.run A n
  let s0 := b + nw.1
  let s1 := s0 + k
  let size := s1 + 10
  let draw := 67108864 * size
  let c0 := n + m
  let c1 := c0 + k
  let count := c1 + 69
  let stride := draw + 1
  let pool := count * stride
  let target := pool + 1
  let address := GeneralPaperStoredWordLength.run A target
  let p0 := price model A b nw.1 s0
  let p1 := price model A s0 k s1
  let p2 := price model A s1 10 size
  let p3 := price model A 67108864 size draw
  let p4 := price model A n m c0
  let p5 := price model A c0 k c1
  let p6 := price model A c1 69 count
  let p7 := price model A draw 1 stride
  let p8 := price model A count stride pool
  let p9 := price model A pool 1 target
  let F := (GeneralPaperEqualAddressConstruction.run model A n m k b).2
  have hF : F = nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + address.2 + 128 * A + 128 := rfl
  have hn := GeneralPaperWordLengthLifetime.bounded A n
  change GeneralPaperWordLengthLifetime.footprint A n ≤ 32 * nw.2 at hn
  have ht := GeneralPaperWordLengthLifetime.bounded A target
  change GeneralPaperWordLengthLifetime.footprint A target ≤ 32 * address.2 at ht
  have h0 := scalar_bound model A b nw.1 s0
  change scalarFoot model A b nw.1 s0 ≤ 32 * p0 at h0
  have h1 := scalar_bound model A s0 k s1
  change scalarFoot model A s0 k s1 ≤ 32 * p1 at h1
  have h2 := scalar_bound model A s1 10 size
  change scalarFoot model A s1 10 size ≤ 32 * p2 at h2
  have h3 := scalar_bound model A 67108864 size draw
  change scalarFoot model A 67108864 size draw ≤ 32 * p3 at h3
  have h4 := scalar_bound model A n m c0
  change scalarFoot model A n m c0 ≤ 32 * p4 at h4
  have h5 := scalar_bound model A c0 k c1
  change scalarFoot model A c0 k c1 ≤ 32 * p5 at h5
  have h6 := scalar_bound model A c1 69 count
  change scalarFoot model A c1 69 count ≤ 32 * p6 at h6
  have h7 := scalar_bound model A draw 1 stride
  change scalarFoot model A draw 1 stride ≤ 32 * p7 at h7
  have h8 := scalar_bound model A count stride pool
  change scalarFoot model A count stride pool ≤ 32 * p8 at h8
  have h9 := scalar_bound model A pool 1 target
  change scalarFoot model A pool 1 target ≤ 32 * p9 at h9
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2) [nw.2, nw.2 + p0, nw.2 + p0 + p1, nw.2 + p0 + p1 + p2, nw.2 + p0 + p1 + p2 + p3, nw.2 + p0 + p1 + p2 + p3 + p4, nw.2 + p0 + p1 + p2 + p3 + p4 + p5, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + address.2, F] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega))
  change fields A _ ≤ 13 * (F + 2 + A) + 32 * A at hFields
  change GeneralPaperWordLengthLifetime.footprint A n +
    scalarFoot model A b nw.1 s0 +
    scalarFoot model A s0 k s1 +
    scalarFoot model A s1 10 size +
    scalarFoot model A 67108864 size draw +
    scalarFoot model A n m c0 +
    scalarFoot model A c0 k c1 +
    scalarFoot model A c1 69 count +
    scalarFoot model A draw 1 stride +
    scalarFoot model A count stride pool +
    scalarFoot model A pool 1 target +
    GeneralPaperWordLengthLifetime.footprint A target + fields A [nw.2, nw.2 + p0, nw.2 + p0 + p1, nw.2 + p0 + p1 + p2, nw.2 + p0 + p1 + p2 + p3, nw.2 + p0 + p1 + p2 + p3 + p4, nw.2 + p0 + p1 + p2 + p3 + p4 + p5, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9, nw.2 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + address.2, F] + 256 * A ≤ 1024 * F
  omega

theorem input_words (model : RationalCostModel) (A n m k b : ℕ) :
    let F := (GeneralPaperEqualAddressConstruction.run model A n m k b).2
    natBits n ≤ F ∧ natBits m ≤ F ∧ natBits k ≤ F ∧ natBits b ≤ F := by
  unfold GeneralPaperEqualAddressConstruction.run
  dsimp only
  unfold price GeneralPaperNaturalScalarStep.word natBits
  omega

theorem output_word (model : RationalCostModel) (A n m k b : ℕ) :
    natBits (GeneralPaperEqualAddressConstruction.run model A n m k b).1 ≤
      (GeneralPaperEqualAddressConstruction.run model A n m k b).2 := by
  unfold GeneralPaperEqualAddressConstruction.run GeneralPaperStoredWordLength.run
  dsimp only
  unfold natBits
  omega

def profile (model : RationalCostModel) (A n m k b : ℕ) : ℕ :=
  1048576 * (model.rat (GeneralPaperEqualAddressConstruction.operandWidth n m k b) + A + 1)

theorem input_bound (model : RationalCostModel) (A n m k b : ℕ) :
    footprint model A n m k b ≤ profile model A n m k b :=
  (bounded model A n m k b).trans ((Nat.mul_le_mul_left 1024
    (GeneralPaperEqualAddressConstruction.work model A n m k b)).trans_eq (by unfold profile; ring))

end Blotto.GeneralPaperAddressConstructionLifetime
