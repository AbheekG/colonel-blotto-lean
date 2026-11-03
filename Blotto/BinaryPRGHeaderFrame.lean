import Blotto.BinaryStoredNatHeader
import Blotto.BinaryPRGMeasuredPreparation

/-! Original dimension payloads produce a retained canonical Boolean header
while the existing decoder supplies the numeric array index. Game framing then
uses that one dimension read and retains header bytes/visits for output reuse.
All decoded canonical game words/suffixes equal the original parser. Numeric
dimension decoding and full frame/control/physical prices remain separate. -/

namespace Blotto.BinaryPRGHeaderFrame
open BinaryRationalNormalization BinaryPRGFrame

structure Header (n : ℕ) where
  bytes : List Bool
  correct : bytes = BinaryNatFrame.encode n
  visits : ℕ
  sourceWidth : ℕ
  visits_bound : visits ≤ 11 * sourceWidth + 12

def readHeader (bits : List Bool) : Option ((Σ n, Header n) × List Bool) :=
  (PositiveBinaryWord.readPayload bits).map (fun raw =>
    let header := BinaryStoredNatHeader.prepare raw.1
    let n := BinaryPayload.decode raw.1
    let prepared : Header n := ⟨header.1,(by rw [BinaryStoredNatHeader.prepare_state,BinaryBigEndian.littleValue_decode]),
      header.2,raw.1.length,BinaryStoredNatHeader.prepare_bound raw.1⟩
    (⟨n,prepared⟩,raw.2))

theorem readHeader_state (bits : List Bool) :
    (readHeader bits).map (fun parsed => (parsed.1.1,parsed.2)) = BinaryNatFrame.read bits := by
  unfold readHeader
  rw [Option.map_map]
  exact PositiveBinaryWord.readPayload_decode bits

theorem readPayload_length_bound (bits payload suffix : List Bool)
    (h : PositiveBinaryWord.readPayload bits = some (payload,suffix)) : payload.length ≤ bits.length := by
  rw [PositiveBinaryWord.readPayload_refines] at h
  unfold PositiveBinaryWord.readPayloadNumeric at h
  cases hs : BinaryNatFrame.scanWidth 0 bits with
  | none => rw [hs,Option.bind_none] at h; cases h
  | some pair =>
      rcases pair with ⟨count,rest⟩
      rw [hs,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hl := BinaryNatFrame.scanWidth_length 0 bits count rest hs
        simp only [List.length_take]
        exact (min_le_right _ _).trans (by omega)
      · cases h

theorem readHeader_sourceWidth_bound (bits : List Bool) (parsed : (Σ n, Header n) × List Bool)
    (h : readHeader bits = some parsed) : parsed.1.2.sourceWidth ≤ bits.length := by
  unfold readHeader at h
  obtain ⟨raw,hRaw,hOut⟩ := Option.map_eq_some_iff.mp h
  subst parsed
  exact readPayload_length_bound bits raw.1 raw.2 hRaw

structure Parsed (n : ℕ) where
  game : BinaryPRGFrame.Parsed n
  header : Header n
  rows : List SignedWord
  rows_length : rows.length = n
  rows_readback : rows = List.ofFn game.input.values.read

def read (bits : List Bool) : Option ((Σ n, Parsed n) × List Bool) :=
  (readHeader bits).bind (fun dim =>
    (readCanonical dim.2).bind (fun first =>
      (readCanonical first.2).bind (fun second =>
        (readWords dim.1.1 second.2).map (fun rest =>
          (⟨dim.1.1,⟨⟨⟨first.1.val,second.1.val,rest.1.table⟩,
            first.1.property,second.1.property,rest.1.table_canonical⟩,dim.1.2,
            rest.1.row,rest.1.length,rest.1.row_eq_ofFn_table⟩⟩,rest.2)))))

def forget (parsed : (Σ n, Parsed n) × List Bool) : (Σ n, BinaryPRGFrame.Parsed n) × List Bool :=
  (⟨parsed.1.1,parsed.1.2.game⟩,parsed.2)

theorem read_state (bits : List Bool) : (read bits).map forget = BinaryPRGFrame.read bits := by
  have hd := readHeader_state bits
  cases h : readHeader bits with
  | none =>
      rw [h,Option.map_none] at hd
      simp only [read,BinaryPRGFrame.read,h,← hd,Option.bind_none,Option.map_none]
  | some dim =>
      rw [h,Option.map_some] at hd
      simp only [read,BinaryPRGFrame.read,h,← hd,Option.bind_some,Option.map_bind]
      apply congrArg (Option.bind (readCanonical dim.2))
      funext first
      simp only [Function.comp_def,Option.map_bind]
      apply congrArg (Option.bind (readCanonical first.2))
      funext second
      simp only [Option.map_map,Function.comp_def,forget]

def readWithVisits (bits : List Bool) : Option ((Σ n, Parsed n) × List Bool) × ℕ :=
  match readHeader bits with
  | none => (none,0)
  | some dim =>
      let parsed := (readCanonical dim.2).bind (fun first =>
        (readCanonical first.2).bind (fun second =>
          (readWords dim.1.1 second.2).map (fun rest =>
            (⟨dim.1.1,⟨⟨⟨first.1.val,second.1.val,rest.1.table⟩,
              first.1.property,second.1.property,rest.1.table_canonical⟩,dim.1.2,
              rest.1.row,rest.1.length,rest.1.row_eq_ofFn_table⟩⟩,rest.2))))
      (parsed,dim.1.2.visits)

theorem readWithVisits_state (bits : List Bool) : (readWithVisits bits).1 = read bits := by
  unfold readWithVisits read
  cases he : readHeader bits <;> rfl

theorem readWithVisits_recorded (bits : List Bool) : (readWithVisits bits).2 ≤
    match readHeader bits with
    | none => 0
    | some dim => 11 * dim.1.2.sourceWidth + 12 := by
  unfold readWithVisits
  cases he : readHeader bits
  · exact Nat.zero_le _
  · exact Header.visits_bound _

theorem readWithVisits_bound (bits : List Bool) : (readWithVisits bits).2 ≤ 11 * bits.length + 12 := by
  have hr := readWithVisits_recorded bits
  cases he : readHeader bits with
  | none => simp only [he] at hr; exact hr.trans (Nat.zero_le _)
  | some parsed =>
      simp only [he] at hr
      exact hr.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 11 (readHeader_sourceWidth_bound bits parsed he)) 12)

structure Checked (n : ℕ) where
  prepared : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid}
  header : Header n
  rows : List SignedWord
  rows_length : rows.length = n

def readChecked (bits : List Bool) : Option ((Σ n, Checked n) × List Bool) × BinaryPRGMeasuredPreparation.Ledger :=
  match read bits with
  | none => (none,⟨0,0⟩)
  | some parsed =>
      let checked := BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical
      (checked.1.map (fun result => (⟨parsed.1.1,⟨result,parsed.1.2.header,
        parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2)),checked.2)

def forgetChecked (parsed : (Σ n, Checked n) × List Bool) :
    (Σ n, {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid}) × List Bool :=
  (⟨parsed.1.1,parsed.1.2.prepared⟩,parsed.2)

theorem readChecked_state (bits : List Bool) : (readChecked bits).1.map forgetChecked = BinaryPRGFrame.readChecked bits := by
  have hp := read_state bits
  cases he : read bits with
  | none =>
      rw [he,Option.map_none] at hp
      simp only [readChecked,he,Option.map_none,BinaryPRGFrame.readChecked,← hp,Option.bind_none]
  | some parsed =>
      rw [he,Option.map_some] at hp
      simp only [readChecked,he,BinaryPRGFrame.readChecked,← hp,Option.bind_some,
        BinaryPRGMeasuredPreparation.prepareChecked_state,Option.map_map,Function.comp_def,forgetChecked,forget]

theorem readChecked_bound (bits : List Bool) :
    (readChecked bits).2.recorded ≤ match read bits with
      | none => 0
      | some parsed => BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input := by
  unfold readChecked
  cases he : read bits
  · exact Nat.zero_le _
  · exact BinaryPRGMeasuredPreparation.prepareChecked_bound _ _

end Blotto.BinaryPRGHeaderFrame
