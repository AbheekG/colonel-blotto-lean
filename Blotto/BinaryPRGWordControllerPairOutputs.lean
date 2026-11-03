import Blotto.BinaryPRGWordControllerPairRegisters

/-! The reached pair exposes lower/upper/probability words by concrete Boolean
register addresses, retaining its own quadratic register and field-read prices.
No native register array is materialized or read by these producers.  Exact
old bytes/canonical values allow the actual resource choice caller to adopt
this interface; that caller replacement is a separately tracked join. -/

namespace Blotto.BinaryPRGWordControllerPairOutputs
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters

structure Outputs where
  lower : SignedWord
  upper : SignedWord
  probability : SignedWord

def prepare (source : BinaryRationalPairProgram.Source) : Outputs :=
  let registers := pair source
  ⟨lookup registers.tree a7,lookup registers.tree a8,lookup registers.tree a11⟩

theorem prepare_words (source : BinaryRationalPairProgram.Source) :
    (prepare source).lower = BinaryRationalRegisterProgram.read source.run 7 ∧
      (prepare source).upper = BinaryRationalRegisterProgram.read source.run 8 ∧
        (prepare source).probability = BinaryRationalRegisterProgram.read source.run 11 := by
  unfold prepare
  dsimp only
  exact ⟨pair_lower source,pair_upper source,pair_probability source⟩

theorem prepare_canonical (source : BinaryRationalPairProgram.Source) :
    CanonicalWord (prepare source).lower ∧ CanonicalWord (prepare source).upper ∧
      CanonicalWord (prepare source).probability := by
  rw [(prepare_words source).1,(prepare_words source).2.1,(prepare_words source).2.2]
  exact ⟨source.run_canonical 7,source.run_canonical 8,source.run_canonical 11⟩

theorem prepare_values (source : BinaryRationalPairProgram.Source) :
    value (prepare source).lower = source.pair.lower ∧ value (prepare source).upper = source.pair.upper ∧
      value (prepare source).probability = source.pair.probability := by
  rw [(prepare_words source).1,(prepare_words source).2.1,(prepare_words source).2.2]
  exact ⟨source.run_lower,source.run_upper,source.run_probability⟩

def prepareWithWork (source : BinaryRationalPairProgram.Source) : Outputs × ℕ :=
  let registers := preparedPairWithWork source
  (⟨lookup registers.1.tree a7,lookup registers.1.tree a8,lookup registers.1.tree a11⟩,
    registers.2 + lookupCells registers.1.tree a7 + lookupCells registers.1.tree a8 +
      lookupCells registers.1.tree a11 + 6)

theorem prepareWithWork_erasure (source : BinaryRationalPairProgram.Source) :
    (prepareWithWork source).1 = prepare source := by
  unfold prepareWithWork prepare
  dsimp only
  rw [preparedPairWithWork_erasure]

def bound (s : ℕ) : ℕ :=
  let W := 32 * s + 31
  218 + 16 * (1 + 2 * W) + 7 * (instructionBound W + 2) + 1 + 3 * (47 + 2 * W) + 6

theorem prepareWithWork_bound (source : BinaryRationalPairProgram.Source) (s : ℕ)
    (hs : 2 ≤ s) (h : source.pair.FieldsHeight s) : (prepareWithWork source).2 ≤ bound s := by
  have hProgram := preparedPairWithWork_bound source s hs h
  have hWidths := source.run_wordBounds h hs
  have h0 := BinaryRationalExpression.payloadWords_bound _ (32 * s + 31) (hWidths 7)
  have h1 := BinaryRationalExpression.payloadWords_bound _ (32 * s + 31) (hWidths 8)
  have h2 := BinaryRationalExpression.payloadWords_bound _ (32 * s + 31) (hWidths 11)
  unfold prepareWithWork bound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact,lookupCells_exact]
  rw [preparedPairWithWork_erasure,pair_lower,pair_upper,pair_probability]
  omega

end Blotto.BinaryPRGWordControllerPairOutputs
