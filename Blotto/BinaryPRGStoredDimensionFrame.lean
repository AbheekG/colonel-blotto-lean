import Blotto.BinaryStoredDimensionRow
import Blotto.BinaryStoredDimensionHeader
import Blotto.BinaryPRGInputPolynomial

/-! The game parser uses a retained Boolean dimension/header and a native
Boolean countdown for its row. Only a successfully returned row supplies the
numeric dimension. Every original canonical word/header/suffix and rejection
scope is preserved. Recorded Boolean/framing/normalization/cell visits derive
from incoming length; small row-size scalars, array/controller/physical and
whole-machine/space costs remain separate. -/

namespace Blotto.BinaryPRGStoredDimensionFrame
open BinaryRationalNormalization BinaryPRGFrame BinaryPRGHeaderFrame

structure Ledger where
  header : ℕ
  budgets : ℕ
  row : ℕ
  rowSizeVisits : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.header + ledger.budgets + ledger.row + ledger.rowSizeVisits

def pack {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // BinaryRationalEncoding.CanonicalWord word}) (rest : Words n × List Bool) :
    (Σ m, BinaryPRGHeaderFrame.Parsed m) × List Bool :=
  let m := rest.1.row.length
  let resized : Words m := ⟨rest.1.row,rfl,rest.1.canonical⟩
  let retained : BinaryPRGHeaderFrame.Header m :=
    ⟨header.bytes,(by change header.bytes = BinaryNatFrame.encode rest.1.row.length
                      rw [rest.1.length]; exact header.correct),header.visits,header.sourceWidth,header.visits_bound⟩
  (⟨m,⟨⟨⟨first.val,second.val,resized.table⟩,first.property,second.property,resized.table_canonical⟩,retained,
    rest.1.row,rfl,resized.row_eq_ofFn_table⟩⟩,rest.2)

theorem pack_state {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // BinaryRationalEncoding.CanonicalWord word}) (rest : Words n × List Bool) :
    pack header first second rest =
      (⟨n,⟨⟨⟨first.val,second.val,rest.1.table⟩,first.property,second.property,rest.1.table_canonical⟩,header,
        rest.1.row,rest.1.length,rest.1.row_eq_ofFn_table⟩⟩,rest.2) := by
  rcases rest with ⟨⟨row,hl,hc⟩,suffix⟩
  subst n
  rfl

def read (bits : List Bool) : Option ((Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool) × Ledger :=
  let dimension := BinaryStoredDimensionHeader.read bits
  match dimension.1 with
  | none => (none,⟨dimension.2,0,0,0⟩)
  | some raw =>
      let first := BinaryCanonicalFrameWork.read raw.2
      match first.1 with
      | none => (none,⟨dimension.2,first.2.recorded,0,0⟩)
      | some firstWord =>
          let second := BinaryCanonicalFrameWork.read firstWord.2
          match second.1 with
          | none => (none,⟨dimension.2,first.2.recorded + second.2.recorded,0,0⟩)
          | some secondWord =>
              let words := BinaryStoredDimensionRow.read raw.1.payload secondWord.2
              let parsed := words.1.map (pack raw.1.typed firstWord.1 secondWord.1)
              let rowSizeVisits := match words.1 with
                | none => 0
                | some rest => rest.1.row.length + 1
              (parsed,⟨dimension.2,first.2.recorded + second.2.recorded,words.2,rowSizeVisits⟩)

theorem read_state (bits : List Bool) : (read bits).1 = BinaryPRGHeaderFrame.read bits := by
  have hh := BinaryStoredDimensionHeader.read_state bits
  unfold read BinaryPRGHeaderFrame.read
  cases hd : (BinaryStoredDimensionHeader.read bits).1 with
  | none =>
      rw [hd,Option.map_none] at hh
      simp only [hd,← hh,Option.bind_none]
  | some raw =>
      rw [hd,Option.map_some] at hh
      simp only [hd,← hh,Option.bind_some,BinaryStoredDimensionHeader.interpret]
      rw [← BinaryCanonicalFrameWork.read_state raw.2]
      cases hf : (BinaryCanonicalFrameWork.read raw.2).1 with
      | none => rfl
      | some first =>
          dsimp only [Option.bind_some]
          rw [← BinaryCanonicalFrameWork.read_state first.2]
          cases hs : (BinaryCanonicalFrameWork.read first.2).1 with
          | none => rfl
          | some second =>
              simp only [Option.bind_some,BinaryStoredDimensionRow.read_state,BinaryCanonicalRowReadWork.read_state]
              apply congrArg (Option.map · (BinaryPRGFrame.readWords (BinaryBigEndian.littleValue raw.1.payload) second.2))
              funext rest
              exact pack_state raw.1.typed first.1 second.1 rest

def bound (length : ℕ) : ℕ := 12 * length + 13 + 2 * BinaryCanonicalFrameWork.bound length +
  BinaryStoredDimensionRow.bound length length + (length + 1)

theorem read_bound (bits : List Bool) : (read bits).2.recorded ≤ bound bits.length := by
  have hh := BinaryStoredDimensionHeader.read_bound bits
  unfold read
  dsimp only
  split
  · change (BinaryStoredDimensionHeader.read bits).2 + 0 + 0 + 0 ≤ _
    unfold bound
    omega
  · rename_i raw hd
    have hRaw := BinaryStoredDimensionHeader.read_suffix_length bits raw hd
    have hWidth := BinaryStoredDimensionHeader.read_payload_length bits raw hd
    have hFirst := (BinaryCanonicalFrameWork.read_bound raw.2).trans (BinaryCanonicalFrameWork.bound_mono hRaw)
    split
    · change (BinaryStoredDimensionHeader.read bits).2 + (BinaryCanonicalFrameWork.read raw.2).2.recorded + 0 + 0 ≤ _
      unfold bound
      omega
    · rename_i first hf
      have hFirstLen := (BinaryCanonicalFrameWork.read_suffix_lt raw.2 first hf).le.trans hRaw
      have hSecond := (BinaryCanonicalFrameWork.read_bound first.2).trans (BinaryCanonicalFrameWork.bound_mono hFirstLen)
      split
      · change (BinaryStoredDimensionHeader.read bits).2 +
          ((BinaryCanonicalFrameWork.read raw.2).2.recorded + (BinaryCanonicalFrameWork.read first.2).2.recorded) + 0 + 0 ≤ _
        unfold bound
        omega
      · rename_i second hs
        have hSecondLen := (BinaryCanonicalFrameWork.read_suffix_lt first.2 second hs).le.trans hFirstLen
        have hRow := (BinaryStoredDimensionRow.read_bound raw.1.payload second.2).trans
          (BinaryStoredDimensionRow.bound_mono hWidth hSecondLen)
        have hSize : (match (BinaryStoredDimensionRow.read raw.1.payload second.2).1 with
            | none => 0
            | some rest => rest.1.row.length + 1) ≤ bits.length + 1 := by
          cases hw : (BinaryStoredDimensionRow.read raw.1.payload second.2).1 with
          | none => exact Nat.zero_le _
          | some rest =>
              have hc := (BinaryStoredDimensionRow.read_count_bound raw.1.payload second.2 rest hw).trans hSecondLen
              change rest.1.row.length + 1 ≤ bits.length + 1
              rw [rest.1.length]
              omega
        change (BinaryStoredDimensionHeader.read bits).2 +
          ((BinaryCanonicalFrameWork.read raw.2).2.recorded + (BinaryCanonicalFrameWork.read first.2).2.recorded) +
          (BinaryStoredDimensionRow.read raw.1.payload second.2).2 +
          (match (BinaryStoredDimensionRow.read raw.1.payload second.2).1 with
           | none => 0
           | some rest => rest.1.row.length + 1) ≤ _
        unfold bound
        omega

theorem bound_polynomial (length : ℕ) : bound length ≤ 538 * (length + 1) ^ 4 := by
  have hb := BinaryPRGInputPolynomial.canonicalFrame_bound length
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  have hp2 := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 2 ≤ 4)
  have hh : 12 * length + 13 ≤ 13 * (length + 1) ^ 4 := by nlinarith
  have hc : (2 + (length + 1)) * BinaryCanonicalFrameWork.bound length ≤
      (3 * (length + 1)) * (173 * (length + 1) ^ 3) := Nat.mul_le_mul (by omega) hb
  calc
    _ = 12 * length + 13 + (2 + (length + 1)) * BinaryCanonicalFrameWork.bound length +
        5 * (length + 1) ^ 2 + (length + 1) := by unfold bound BinaryStoredDimensionRow.bound; ring
    _ ≤ 13 * (length + 1) ^ 4 + (3 * (length + 1)) * (173 * (length + 1) ^ 3) +
        5 * (length + 1) ^ 4 + (length + 1) ^ 4 := by gcongr
    _ = _ := by ring

theorem read_polynomial (bits : List Bool) : (read bits).2.recorded ≤ 538 * (bits.length + 1) ^ 4 :=
  (read_bound bits).trans (bound_polynomial bits.length)

end Blotto.BinaryPRGStoredDimensionFrame
