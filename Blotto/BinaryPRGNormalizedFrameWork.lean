import Blotto.BinaryNatFrameDecodingCost
import Blotto.BinaryCanonicalRowReadWork

/-! Actual header-preserving game parsing uses measured canonical word reads
and the measured row loop. Exact old canonical words/suffix/header and rejection
are retained. Frame length derives normalization/framing/header Boolean prices,
including huge failed dimensions. Numeric dimension decoding, array/control/
bookkeeping/physical costs remain separate. -/

namespace Blotto.BinaryPRGNormalizedFrameWork
open BinaryRationalNormalization BinaryPRGFrame BinaryPRGHeaderFrame

structure Ledger where
  header : ℕ
  canonicalWords : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.header + ledger.canonicalWords

def read (bits : List Bool) : Option ((Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool) × Ledger :=
  match BinaryPRGHeaderFrame.readHeader bits with
  | none => (none,⟨0,0⟩)
  | some dim =>
      let first := BinaryCanonicalFrameWork.read dim.2
      match first.1 with
      | none => (none,⟨dim.1.2.visits,first.2.recorded⟩)
      | some firstWord =>
          let second := BinaryCanonicalFrameWork.read firstWord.2
          match second.1 with
          | none => (none,⟨dim.1.2.visits,first.2.recorded + second.2.recorded⟩)
          | some secondWord =>
              let words := BinaryCanonicalRowReadWork.read dim.1.1 secondWord.2
              let parsed := words.1.map (fun rest =>
                (⟨dim.1.1,⟨⟨⟨firstWord.1.val,secondWord.1.val,rest.1.table⟩,
                  firstWord.1.property,secondWord.1.property,rest.1.table_canonical⟩,dim.1.2,
                  rest.1.row,rest.1.length,rest.1.row_eq_ofFn_table⟩⟩,rest.2))
              (parsed,⟨dim.1.2.visits,first.2.recorded + second.2.recorded + words.2⟩)

theorem read_state (bits : List Bool) : (read bits).1 = BinaryPRGHeaderFrame.read bits := by
  unfold read BinaryPRGHeaderFrame.read
  cases hd : BinaryPRGHeaderFrame.readHeader bits with
  | none => rfl
  | some dim =>
      dsimp only [Option.bind_some]
      rw [← BinaryCanonicalFrameWork.read_state dim.2]
      cases hf : (BinaryCanonicalFrameWork.read dim.2).1 with
      | none => rfl
      | some first =>
          dsimp only [Option.bind_some]
          rw [← BinaryCanonicalFrameWork.read_state first.2]
          cases hs : (BinaryCanonicalFrameWork.read first.2).1 with
          | none => rfl
          | some second => simp only [Option.bind_some,BinaryCanonicalRowReadWork.read_state]

theorem read_header (bits : List Bool) : (read bits).2.header = (BinaryPRGHeaderFrame.readWithVisits bits).2 := by
  unfold read BinaryPRGHeaderFrame.readWithVisits
  cases hd : BinaryPRGHeaderFrame.readHeader bits with
  | none => rfl
  | some dim =>
      dsimp only
      split
      · rfl
      · split <;> rfl

theorem header_suffix_length (bits : List Bool) (dim : (Σ n, Header n) × List Bool)
    (h : BinaryPRGHeaderFrame.readHeader bits = some dim) : dim.2.length ≤ bits.length := by
  have he := BinaryPRGHeaderFrame.readHeader_state bits
  rw [h,Option.map_some] at he
  exact BinaryNatFrame.read_suffix_length bits dim.1.1 dim.2 he.symm

def canonicalBound (length : ℕ) : ℕ := 2 * BinaryCanonicalFrameWork.bound length + BinaryCanonicalRowReadWork.bound length

theorem read_canonical_bound (bits : List Bool) : (read bits).2.canonicalWords ≤ canonicalBound bits.length := by
  unfold read
  split
  · exact Nat.zero_le _
  · rename_i dim hDim
    have hDimLen := header_suffix_length bits dim hDim
    have hFirst := (BinaryCanonicalFrameWork.read_bound dim.2).trans (BinaryCanonicalFrameWork.bound_mono hDimLen)
    dsimp only
    split
    · change (BinaryCanonicalFrameWork.read dim.2).2.recorded ≤ _
      unfold canonicalBound; omega
    · rename_i first hFirstSome
      have hFirstLen := (BinaryCanonicalFrameWork.read_suffix_lt dim.2 first hFirstSome).le.trans hDimLen
      have hSecond := (BinaryCanonicalFrameWork.read_bound first.2).trans (BinaryCanonicalFrameWork.bound_mono hFirstLen)
      split
      · change (BinaryCanonicalFrameWork.read dim.2).2.recorded + (BinaryCanonicalFrameWork.read first.2).2.recorded ≤ _
        unfold canonicalBound; omega
      · rename_i second hSecondSome
        have hSecondLen := (BinaryCanonicalFrameWork.read_suffix_lt first.2 second hSecondSome).le.trans hFirstLen
        have hWords := (BinaryCanonicalRowReadWork.read_bound dim.1.1 second.2).trans (BinaryCanonicalRowReadWork.bound_mono hSecondLen)
        change (BinaryCanonicalFrameWork.read dim.2).2.recorded + (BinaryCanonicalFrameWork.read first.2).2.recorded +
          (BinaryCanonicalRowReadWork.read dim.1.1 second.2).2 ≤ _
        unfold canonicalBound
        omega

def bound (length : ℕ) : ℕ := 11 * length + 12 + canonicalBound length

theorem read_bound (bits : List Bool) : (read bits).2.recorded ≤ bound bits.length := by
  have hh := BinaryPRGHeaderFrame.readWithVisits_bound bits
  rw [← read_header] at hh
  exact Nat.add_le_add hh (read_canonical_bound bits)

end Blotto.BinaryPRGNormalizedFrameWork
