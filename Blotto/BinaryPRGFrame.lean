import Blotto.BinaryPRGPreparation
import Blotto.RationalPRGBinaryInput

/-! The actual original-game frame parser retains canonical signed Boolean
words and constructs checked cached PRG preparation. No caller supplies input
canonicality, a rational source, or a successful-promise certificate. The
mathematical interpretation agrees with the original suffix-preserving game
format; the parser never encodes bits from interpreted rational values. -/

namespace Blotto.BinaryPRGFrame
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition BinaryPRGPreparation

structure Words (n : ℕ) where
  row : List SignedWord
  length : row.length = n
  canonical : ∀ word ∈ row, CanonicalWord word

def readCanonical (bits : List Bool) : Option ({word : SignedWord // CanonicalWord word} × List Bool) :=
  match hf : readFrame bits with
  | none => none
  | some parsed => some (⟨parsed.1, readFrame_canonical bits parsed.1 parsed.2 hf⟩, parsed.2)

theorem readCanonical_refines (bits : List Bool) :
    (readCanonical bits).map (fun result => (value result.1.val, result.2)) = BinaryRatFrame.read bits := by
  unfold readCanonical
  split
  · rename_i hs
    simpa only [hs, Option.map_none] using readFrame_refines bits
  · rename_i parsed hs
    exact (readFrame_sound bits parsed.1 parsed.2 hs).symm

def readWords : (n : ℕ) → List Bool → Option (Words n × List Bool)
  | 0, bits => some (⟨[], rfl, by simp⟩, bits)
  | n + 1, bits =>
      (readCanonical bits).bind (fun first =>
          (readWords n first.2).map (fun rest => (⟨first.1.val :: rest.1.row,
              by simp [rest.1.length],
              by
                intro word hw
                rcases List.mem_cons.mp hw with he | ht
                · subst word
                  exact first.1.property
                · exact rest.1.canonical word ht⟩, rest.2)))

def Words.table {n : ℕ} (words : Words n) : FixedArrayTable n SignedWord :=
  ⟨words.row.toArray, by simpa using words.length⟩

theorem Words.table_canonical {n : ℕ} (words : Words n) :
    ∀ j, CanonicalWord (words.table.read j) := by
  intro j
  unfold FixedArrayTable.read Words.table
  simp only [List.getElem_toArray]
  exact words.canonical _ (List.getElem_mem _)

theorem Words.table_values {n : ℕ} (words : Words n) :
    List.ofFn (fun j => value (words.table.read j)) = words.row.map value := by
  apply List.ext_getElem
  · simp [words.length]
  · intro i hLeft hRight
    simp only [List.getElem_ofFn, List.getElem_map, Words.table, FixedArrayTable.read, List.getElem_toArray]

theorem Words.row_eq_ofFn_table {n : ℕ} (words : Words n) :
    words.row = List.ofFn words.table.read := by
  apply List.ext_getElem
  · simp [words.length]
  · intro i hLeft hRight
    simp only [List.getElem_ofFn, Words.table, FixedArrayTable.read, List.getElem_toArray]

theorem readWords_refines (n : ℕ) (bits : List Bool) :
    (readWords n bits).map (fun result => (result.1.row.map value, result.2)) =
      BinaryRatListFrame.read n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
      have hf := readCanonical_refines bits
      cases hs : readCanonical bits with
      | none =>
          rw [hs, Option.map_none] at hf
          simp only [readWords, hs, Option.map_none, BinaryRatListFrame.read, ← hf, Option.bind_none]
      | some first =>
          rw [hs, Option.map_some] at hf
          have ht := ih first.2
          cases hr : readWords n first.2 with
          | none =>
              rw [hr, Option.map_none] at ht
              simp only [readWords, hs, hr, Option.map_none, BinaryRatListFrame.read, ← hf,
                Option.bind_some, ← ht]
          | some rest =>
              rw [hr, Option.map_some] at ht
              simp only [readWords, hs, hr, Option.map_some, List.map_cons, BinaryRatListFrame.read,
                ← hf, Option.bind_some, ← ht, Option.map_some]

structure Parsed (n : ℕ) where
  input : BinaryPRGRecognition.Input n
  canonical : input.Canonical

def read (bits : List Bool) : Option ((Σ n, Parsed n) × List Bool) :=
  (BinaryNatFrame.read bits).bind (fun dim =>
    (readCanonical dim.2).bind (fun first =>
        (readCanonical first.2).bind (fun second =>
            (readWords dim.1 second.2).map (fun rest =>
              (⟨dim.1, ⟨⟨first.1.val, second.1.val, rest.1.table⟩,
                first.1.property, second.1.property,
                rest.1.table_canonical⟩⟩, rest.2)))))

noncomputable def decoded (parsed : Σ n, Parsed n) : BinaryGameWords :=
  ⟨parsed.1, value parsed.2.input.a, value parsed.2.input.b,
    List.ofFn (fun j => value (parsed.2.input.values.read j))⟩

theorem read_refines (bits : List Bool) :
    (read bits).map (fun result => (decoded result.1, result.2)) = RationalPRGBinaryInput.read bits := by
  unfold read RationalPRGBinaryInput.read
  cases hd : BinaryNatFrame.read bits with
  | none => simp only [Option.bind_none, Option.map_none]
  | some dim =>
      simp only [Option.bind_some]
      have ha := readCanonical_refines dim.2
      cases hf : readCanonical dim.2 with
      | none =>
          rw [hf, Option.map_none] at ha
          simp only [← ha, Option.bind_none, Option.map_none]
      | some first =>
          rw [hf, Option.map_some] at ha
          simp only [← ha, Option.bind_some]
          have hb := readCanonical_refines first.2
          cases hs : readCanonical first.2 with
          | none =>
              rw [hs, Option.map_none] at hb
              simp only [← hb, Option.bind_none, Option.map_none]
          | some second =>
              rw [hs, Option.map_some] at hb
              simp only [← hb, Option.bind_some]
              have hr := readWords_refines dim.1 second.2
              cases hw : readWords dim.1 second.2 with
              | none =>
                  rw [hw, Option.map_none] at hr
                  simp only [Option.map_none, ← hr]
              | some rest =>
                  rw [hw, Option.map_some] at hr
                  simp only [Option.map_some, ← hr, decoded, Words.table_values]

def readChecked (bits : List Bool) : Option ((Σ n, {prepared : Prepared n // prepared.Valid}) × List Bool) :=
  (read bits).bind (fun parsed =>
    (prepareChecked parsed.1.2.input parsed.1.2.canonical).map
      (fun result => (⟨parsed.1.1, result⟩, parsed.2)))

theorem readChecked_success (bits suffix : List Bool)
    (result : Σ n, {prepared : Prepared n // prepared.Valid})
    (h : readChecked bits = some (result, suffix)) :
    ∃ parsed : Parsed result.1,
      read bits = some (⟨result.1, parsed⟩, suffix) ∧
      parsed.input.Checks ∧ result.2.val = prepare parsed.input := by
  unfold readChecked at h
  cases hp : read bits with
  | none => rw [hp, Option.bind_none] at h; cases h
  | some parsed =>
      rw [hp, Option.bind_some] at h
      cases hc : prepareChecked parsed.1.2.input parsed.1.2.canonical with
      | none => rw [hc, Option.map_none] at h; cases h
      | some prepared =>
          rw [hc, Option.map_some] at h
          cases Option.some.inj h
          refine ⟨parsed.1.2, rfl, ?_, prepareChecked_data _ _ _ hc⟩
          exact (prepareChecked_isSome _ _).mp (by rw [hc]; rfl)

noncomputable def decodedPrepared (result : Σ n, {prepared : Prepared n // prepared.Valid}) :
    Σ n, RationalPRGOriginalInput n :=
  ⟨result.1, result.2.val.original.source result.2.property.2.2⟩

theorem readChecked_refines (bits : List Bool) :
    (readChecked bits).map (fun result => (decodedPrepared result.1, result.2)) =
      RationalPRGBinaryInput.readChecked bits := by
  have hr := read_refines bits
  cases hp : read bits with
  | none =>
      rw [hp, Option.map_none] at hr
      simp only [readChecked, hp, Option.bind_none, Option.map_none,
        RationalPRGBinaryInput.readChecked, ← hr]
  | some parsed =>
      rw [hp, Option.map_some] at hr
      simp only [readChecked, hp, Option.bind_some, RationalPRGBinaryInput.readChecked,
        ← hr, Option.bind_some, decoded, List.length_ofFn, dite_true, BinaryGameWords.valueTable_ofFn]
      by_cases hc : parsed.1.2.input.Checks
      · have hb := (checkBool_iff parsed.1.2.input parsed.1.2.canonical).mpr hc
        have hs := checkRationalPRG_complete (parsed.1.2.input.source hc)
        change checkRationalPRG (fun j => value (parsed.1.2.input.values.read j))
          (value parsed.1.2.input.a) (value parsed.1.2.input.b) = _ at hs
        simp only [prepareChecked, dite_eq_left hb, Option.map_some, decodedPrepared, prepare_original, hs]
      · have hb : ¬checkBool parsed.1.2.input = true :=
          fun hb => hc ((checkBool_iff parsed.1.2.input parsed.1.2.canonical).mp hb)
        have hs := (checkRationalPRG_none (fun j => value (parsed.1.2.input.values.read j))
          (value parsed.1.2.input.a) (value parsed.1.2.input.b)).mpr hc
        simp only [prepareChecked, dite_eq_right hb, Option.map_none, hs]

end Blotto.BinaryPRGFrame
