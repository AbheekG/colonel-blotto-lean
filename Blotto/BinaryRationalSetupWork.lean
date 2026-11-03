import Blotto.BinaryRationalPairProgram
import Blotto.UnaryPayloadWork
import Blotto.BinaryWordParseBounds

/-! Actual Boolean payload parsing, rational canonicalization and pair interior
recognition have explicit setup prices. Instrumented parsers retain every
malformed and zero-denominator branch and share suffixes. Costs count abstract
Boolean/cell work; they do not certify native CPU, GC or full PRG execution. -/

namespace Blotto.BinaryRationalSetupWork
open BinaryRationalNormalization BinaryRationalOpcode BinaryRationalEncoding

def findPayloadWithWork : List Bool → Option (List Bool) × ℕ
  | [] => (none, 3)
  | true :: rest => (some rest, 3)
  | false :: rest =>
      let later := findPayloadWithWork rest
      (later.1, 3 + later.2)

theorem findPayloadWithWork_state (frame : List Bool) : (findPayloadWithWork frame).1 = UnaryPayload.findPayload frame := by
  induction frame with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [findPayloadWithWork, UnaryPayload.findPayload, ih]

theorem findPayloadWithWork_cost (frame : List Bool) : (findPayloadWithWork frame).2 = 3 * UnaryPayload.findSteps frame := by
  induction frame with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [findPayloadWithWork, UnaryPayload.findSteps, ih]
      omega

def consumeWithWork : List Bool → List Bool → List Bool → Option (List Bool × List Bool) × ℕ
  | [], _payload, _reversed => (none, 4)
  | true :: _ruler, payload, reversed => (some (reversed.reverse, payload), 4 + 2 * reversed.length)
  | false :: _ruler, [], _reversed => (none, 4)
  | false :: ruler, bit :: payload, reversed =>
      let later := consumeWithWork ruler payload (bit :: reversed)
      (later.1, 6 + later.2)

theorem consumeWithWork_state (ruler payload reversed : List Bool) :
    (consumeWithWork ruler payload reversed).1 = UnaryPayload.consume ruler payload reversed := by
  induction ruler generalizing payload reversed with
  | nil => rfl
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => rfl
        | cons bit payload => exact ih payload (bit :: reversed)
      · rfl

theorem consumeWithWork_bound (ruler payload reversed : List Bool) :
    (consumeWithWork ruler payload reversed).2 ≤ 8 * UnaryPayload.consumeCopies ruler payload + 2 * reversed.length + 4 := by
  induction ruler generalizing payload reversed with
  | nil => simp [consumeWithWork, UnaryPayload.consumeCopies]
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => simp [consumeWithWork, UnaryPayload.consumeCopies]
        | cons bit payload =>
            have h := ih payload (bit :: reversed)
            simp only [consumeWithWork, UnaryPayload.consumeCopies, List.length_cons] at h ⊢
            omega
      · simp only [consumeWithWork, UnaryPayload.consumeCopies]
        omega

def readPayloadWithWork (frame : List Bool) : Option (List Bool × List Bool) × ℕ :=
  let found := findPayloadWithWork frame
  match found.1 with
  | none => (none, found.2)
  | some payload =>
      let parsed := consumeWithWork frame payload []
      (parsed.1, found.2 + parsed.2 + 2)

theorem readPayloadWithWork_state (frame : List Bool) :
    (readPayloadWithWork frame).1 = PositiveBinaryWord.readPayload frame := by
  unfold readPayloadWithWork
  dsimp only
  rw [findPayloadWithWork_state]
  change _ = UnaryPayload.read frame
  unfold UnaryPayload.read
  cases h : UnaryPayload.findPayload frame
  · rfl
  · dsimp only
    rw [consumeWithWork_state]
    rfl

theorem readPayloadWithWork_bound (frame : List Bool) : (readPayloadWithWork frame).2 ≤ 11 * frame.length + 9 := by
  have hFind := UnaryPayload.findSteps_bound frame
  unfold readPayloadWithWork
  dsimp only
  rw [findPayloadWithWork_state, findPayloadWithWork_cost]
  cases h : UnaryPayload.findPayload frame
  · dsimp only
    omega
  · rename_i payload
    have hConsume := consumeWithWork_bound frame payload []
    have hCopies := UnaryPayload.consumeCopies_ruler_bound frame payload
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hConsume
    dsimp only
    omega

theorem payload_sizes (frame payload suffix : List Bool)
    (h : PositiveBinaryWord.readPayload frame = some (payload, suffix)) :
    payload.length ≤ frame.length ∧ suffix.length ≤ frame.length := by
  have hs := PositiveBinaryWord.readPayload_length frame payload suffix h
  omega

def readFrameWithWork : List Bool → Option (SignedWord × List Bool) × ℕ
  | [] => (none, 2)
  | negative :: rest =>
      let first := readPayloadWithWork rest
      match first.1 with
      | none => (none, first.2 + 2)
      | some numerator =>
          let second := readPayloadWithWork numerator.2
          match second.1 with
          | none => (none, first.2 + second.2 + 4)
          | some denominator =>
              let cost := first.2 + second.2 + 3 * (denominator.1.length + 1) + 6
              if BinaryEuclideanGCD.nonzero denominator.1 then
                let raw : SignedWord := ⟨negative, numerator.1, denominator.1⟩
                let encoded := canonicalizeWithWork raw
                (some (encoded.1, denominator.2), cost + encoded.2)
              else (none, cost)

theorem readFrameWithWork_state (frame : List Bool) :
    (readFrameWithWork frame).1 = readFrame frame := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      unfold readFrameWithWork
      dsimp only
      rw [readPayloadWithWork_state]
      cases hN : PositiveBinaryWord.readPayload rest
      · simp only [hN, readFrame, Option.bind_none]
      · rename_i numerator
        dsimp only
        rw [readPayloadWithWork_state]
        cases hD : PositiveBinaryWord.readPayload numerator.2
        · simp only [hD, readFrame, hN, Option.bind_some, Option.bind_none]
        · rename_i denominator
          dsimp only
          split <;> simp only [readFrame, hN, hD, Option.bind_some]
          · rename_i hNZ
            rw [ite_eq_left hNZ]
            rfl
          · rename_i hNZ
            rw [ite_eq_right hNZ]

theorem readFrameWithWork_bound (frame : List Bool) :
    (readFrameWithWork frame).2 ≤ 220 * (frame.length + 1) ^ 3 := by
  cases frame with
  | nil => decide
  | cons negative rest =>
      have hNWork := readPayloadWithWork_bound rest
      have hLinear : rest.length + 2 ≤ (rest.length + 2) ^ 3 := by
        have hSq : 1 ≤ (rest.length + 2) ^ 2 := one_le_pow₀ (by omega)
        nlinarith
      unfold readFrameWithWork
      dsimp only
      rw [readPayloadWithWork_state]
      cases hN : PositiveBinaryWord.readPayload rest
      · dsimp only
        simp only [List.length_cons]
        nlinarith
      · rename_i numerator
        rcases numerator with ⟨numBits, numTail⟩
        have hNSize := payload_sizes rest numBits numTail hN
        have hDWork := readPayloadWithWork_bound numTail
        dsimp only
        rw [readPayloadWithWork_state]
        cases hD : PositiveBinaryWord.readPayload numTail
        · dsimp only
          simp only [List.length_cons]
          nlinarith
        · rename_i denominator
          rcases denominator with ⟨denBits, suffix⟩
          have hDSize := payload_sizes numTail denBits suffix hD
          have hWidth : width (⟨negative, numBits, denBits⟩ : SignedWord) ≤ rest.length := by
            unfold width
            dsimp only
            omega
          have hC := canonicalizeWithWork_bound (⟨negative, numBits, denBits⟩ : SignedWord)
          have hPow := Nat.pow_le_pow_left (Nat.add_le_add_right hWidth 1) 3
          have hCBound := hC.trans (Nat.mul_le_mul_left 170 hPow)
          dsimp only
          split <;> simp only [List.length_cons] <;> nlinarith

theorem canonicalize_lengths_le (word : SignedWord) :
    (canonicalize word).numerator.length ≤ word.numerator.length ∧
      (canonicalize word).denominator.length ≤ word.denominator.length := by
  have hn := BinaryCanonicalMagnitude.trim_length (normalize word).numerator
  have hd := BinaryCanonicalMagnitude.trim_length (normalize word).denominator
  rw [(normalize_lengths word).1] at hn
  rw [(normalize_lengths word).2] at hd
  exact ⟨hn, hd⟩

theorem readFrame_sizes (frame : List Bool) (word : SignedWord) (suffix : List Bool)
    (h : readFrame frame = some (word, suffix)) : width word ≤ frame.length ∧ suffix.length ≤ frame.length := by
  cases frame with
  | nil => cases h
  | cons negative rest =>
      unfold readFrame at h
      dsimp only at h
      cases hN : PositiveBinaryWord.readPayload rest with
      | none => rw [hN, Option.bind_none] at h; cases h
      | some numerator =>
          rcases numerator with ⟨numBits, numTail⟩
          rw [hN, Option.bind_some] at h
          have hNSize := payload_sizes rest numBits numTail hN
          cases hD : PositiveBinaryWord.readPayload numTail with
          | none => rw [hD, Option.bind_none] at h; cases h
          | some denominator =>
              rcases denominator with ⟨denBits, tail⟩
              rw [hD, Option.bind_some] at h
              have hDSize := payload_sizes numTail denBits tail hD
              split at h
              · cases Option.some.inj h
                have hLengths := canonicalize_lengths_le (⟨negative, numBits, denBits⟩ : SignedWord)
                change _ ≤ numBits.length ∧ _ ≤ denBits.length at hLengths
                unfold width fromPayload
                simp only [List.length_cons]
                omega
              · cases h

def readFieldsWithWork (frame : List Bool) :
    Option (SignedWord × SignedWord × SignedWord × SignedWord × List Bool) × ℕ :=
  let first := readFrameWithWork frame
  match first.1 with
  | none => (none, first.2)
  | some lengthI =>
      let second := readFrameWithWork lengthI.2
      match second.1 with
      | none => (none, first.2 + second.2 + 2)
      | some lengthJ =>
          let third := readFrameWithWork lengthJ.2
          match third.1 with
          | none => (none, first.2 + second.2 + third.2 + 4)
          | some resourceI =>
              let fourth := readFrameWithWork resourceI.2
              (fourth.1.map (fun resourceJ => (lengthI.1, lengthJ.1, resourceI.1, resourceJ.1, resourceJ.2)),
                first.2 + second.2 + third.2 + fourth.2 + 6)

theorem readFieldsWithWork_state (frame : List Bool) :
    (readFieldsWithWork frame).1 = BinaryRationalPairProgram.readFields frame := by
  unfold readFieldsWithWork
  dsimp only
  rw [readFrameWithWork_state]
  cases h1 : readFrame frame
  · simp [BinaryRationalPairProgram.readFields, h1]
  · rename_i first
    dsimp only
    rw [readFrameWithWork_state]
    cases h2 : readFrame first.2
    · simp [BinaryRationalPairProgram.readFields, h1, h2]
    · rename_i second
      dsimp only
      rw [readFrameWithWork_state]
      cases h3 : readFrame second.2
      · simp [BinaryRationalPairProgram.readFields, h1, h2, h3]
      · rename_i third
        dsimp only
        rw [readFrameWithWork_state]
        simp [BinaryRationalPairProgram.readFields, h1, h2, h3]

theorem readFieldsWithWork_bound (frame : List Bool) :
    (readFieldsWithWork frame).2 ≤ 900 * (frame.length + 1) ^ 3 := by
  have h1w := readFrameWithWork_bound frame
  have hp : 1 ≤ (frame.length + 1) ^ 3 := one_le_pow₀ (by omega)
  unfold readFieldsWithWork
  dsimp only
  rw [readFrameWithWork_state]
  cases h1 : readFrame frame
  · dsimp only
    omega
  · rename_i first
    rcases first with ⟨lengthI, rest1⟩
    have h1s := (readFrame_sizes frame lengthI rest1 h1).2
    have h2w := (readFrameWithWork_bound rest1).trans (Nat.mul_le_mul_left 220
      (Nat.pow_le_pow_left (Nat.add_le_add_right h1s 1) 3))
    dsimp only
    rw [readFrameWithWork_state]
    cases h2 : readFrame rest1
    · dsimp only
      nlinarith
    · rename_i second
      rcases second with ⟨lengthJ, rest2⟩
      have h2s := ((readFrame_sizes rest1 lengthJ rest2 h2).2).trans h1s
      have h3w := (readFrameWithWork_bound rest2).trans (Nat.mul_le_mul_left 220
        (Nat.pow_le_pow_left (Nat.add_le_add_right h2s 1) 3))
      dsimp only
      rw [readFrameWithWork_state]
      cases h3 : readFrame rest2
      · dsimp only
        nlinarith
      · rename_i third
        rcases third with ⟨resourceI, rest3⟩
        have h3s := ((readFrame_sizes rest2 resourceI rest3 h3).2).trans h2s
        have h4w := (readFrameWithWork_bound rest3).trans (Nat.mul_le_mul_left 220
          (Nat.pow_le_pow_left (Nat.add_le_add_right h3s 1) 3))
        dsimp only
        nlinarith

def interiorWork (length resource : SignedWord) : ℕ :=
  BinaryRationalArithmetic.lessEqualWork resource zero + BinaryRationalArithmetic.lessEqualWork length resource + 3

theorem interiorWork_bound (length resource : SignedWord) (W : ℕ) (hL : width length ≤ W)
    (hR : width resource ≤ W) (hW : 1 ≤ W) : interiorWork length resource ≤ 1000 * (W + 1) ^ 2 + 3 := by
  have hZero : width zero = 1 := rfl
  have hFirst := BinaryRationalArithmetic.lessEqualWork_bound resource zero
  have hSecond := BinaryRationalArithmetic.lessEqualWork_bound length resource
  have hw1 : BinaryRationalArithmetic.pairWidth resource zero ≤ W := by
    unfold BinaryRationalArithmetic.pairWidth
    rw [hZero]
    omega
  have hw2 : BinaryRationalArithmetic.pairWidth length resource ≤ W := max_le hL hR
  have h1 := hFirst.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hw1 1) 2))
  have h2 := hSecond.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hw2 1) 2))
  unfold interiorWork
  omega

def checkWithWork (lengthI lengthJ resourceI resourceJ : SignedWord)
    (hLI : CanonicalWord lengthI) (hLJ : CanonicalWord lengthJ)
    (hRI : CanonicalWord resourceI) (hRJ : CanonicalWord resourceJ) :
    Option BinaryRationalPairProgram.Source × ℕ :=
  (BinaryRationalPairProgram.fromCanonicalChecked lengthI lengthJ resourceI resourceJ hLI hLJ hRI hRJ,
    interiorWork lengthI resourceI + interiorWork lengthJ resourceJ + 2)

theorem checkWithWork_bound (lengthI lengthJ resourceI resourceJ : SignedWord)
    (hLI : CanonicalWord lengthI) (hLJ : CanonicalWord lengthJ)
    (hRI : CanonicalWord resourceI) (hRJ : CanonicalWord resourceJ) (W : ℕ) (hW : 1 ≤ W)
    (hwLI : width lengthI ≤ W) (hwLJ : width lengthJ ≤ W) (hwRI : width resourceI ≤ W) (hwRJ : width resourceJ ≤ W) :
    (checkWithWork lengthI lengthJ resourceI resourceJ hLI hLJ hRI hRJ).2 ≤ 2000 * (W + 1) ^ 2 + 8 := by
  have hI := interiorWork_bound lengthI resourceI W hwLI hwRI hW
  have hJ := interiorWork_bound lengthJ resourceJ W hwLJ hwRJ hW
  unfold checkWithWork
  omega

def checkInteriorWithWork (length resource : SignedWord) : Bool × ℕ :=
  let first := BinaryRationalArithmetic.lessEqual resource zero
  let second := BinaryRationalArithmetic.lessEqual length resource
  ((!first && !second), interiorWork length resource)

theorem checkInteriorWithWork_state (length resource : SignedWord) :
    (checkInteriorWithWork length resource).1 = BinaryRationalPairProgram.checkInterior length resource := rfl

structure ParsedFields where
  lengthI : SignedWord
  lengthJ : SignedWord
  resourceI : SignedWord
  resourceJ : SignedWord
  suffix : List Bool
  lengthI_canonical : CanonicalWord lengthI
  lengthJ_canonical : CanonicalWord lengthJ
  resourceI_canonical : CanonicalWord resourceI
  resourceJ_canonical : CanonicalWord resourceJ

def readFieldsCertifiedWithWork (frame : List Bool) : Option ParsedFields × ℕ :=
  let first := readFrameWithWork frame
  match h1 : first.1 with
  | none => (none, first.2)
  | some lengthI =>
      let second := readFrameWithWork lengthI.2
      match h2 : second.1 with
      | none => (none, first.2 + second.2 + 2)
      | some lengthJ =>
          let third := readFrameWithWork lengthJ.2
          match h3 : third.1 with
          | none => (none, first.2 + second.2 + third.2 + 4)
          | some resourceI =>
              let fourth := readFrameWithWork resourceI.2
              match h4 : fourth.1 with
              | none => (none, first.2 + second.2 + third.2 + fourth.2 + 6)
              | some resourceJ =>
                  (some ⟨lengthI.1, lengthJ.1, resourceI.1, resourceJ.1, resourceJ.2,
                    readFrame_canonical frame _ _ ((readFrameWithWork_state frame).symm.trans h1),
                    readFrame_canonical lengthI.2 _ _ ((readFrameWithWork_state lengthI.2).symm.trans h2),
                    readFrame_canonical lengthJ.2 _ _ ((readFrameWithWork_state lengthJ.2).symm.trans h3),
                    readFrame_canonical resourceI.2 _ _ ((readFrameWithWork_state resourceI.2).symm.trans h4)⟩,
                    first.2 + second.2 + third.2 + fourth.2 + 6)

theorem readFieldsCertifiedWithWork_cost (frame : List Bool) :
    (readFieldsCertifiedWithWork frame).2 = (readFieldsWithWork frame).2 := by
  unfold readFieldsCertifiedWithWork
  dsimp only
  split
  · rename_i h1
    simp only [readFieldsWithWork, h1]
  · rename_i first h1
    split
    · rename_i h2
      simp only [readFieldsWithWork, h1, h2]
    · rename_i second h2
      split
      · rename_i h3
        simp only [readFieldsWithWork, h1, h2, h3]
      · rename_i third h3
        split <;> simp only [readFieldsWithWork, h1, h2, h3]

theorem readFieldsCertifiedWithWork_sizes (frame : List Bool) (parsed : ParsedFields)
    (h : (readFieldsCertifiedWithWork frame).1 = some parsed) :
    width parsed.lengthI ≤ frame.length ∧ width parsed.lengthJ ≤ frame.length ∧
      width parsed.resourceI ≤ frame.length ∧ width parsed.resourceJ ≤ frame.length := by
  unfold readFieldsCertifiedWithWork at h
  dsimp only at h
  split at h
  · cases h
  · rename_i first h1
    have hs1 := readFrame_sizes frame first.1 first.2 ((readFrameWithWork_state frame).symm.trans h1)
    split at h
    · cases h
    · rename_i second h2
      have hs2 := readFrame_sizes first.2 second.1 second.2 ((readFrameWithWork_state first.2).symm.trans h2)
      split at h
      · cases h
      · rename_i third h3
        have hs3 := readFrame_sizes second.2 third.1 third.2 ((readFrameWithWork_state second.2).symm.trans h3)
        split at h
        · cases h
        · rename_i fourth h4
          have hs4 := readFrame_sizes third.2 fourth.1 fourth.2 ((readFrameWithWork_state third.2).symm.trans h4)
          cases Option.some.inj h
          exact ⟨hs1.1, hs2.1.trans hs1.2, hs3.1.trans (hs2.2.trans hs1.2),
            hs4.1.trans (hs3.2.trans (hs2.2.trans hs1.2))⟩

def parsedCheckWithWork (parsed : ParsedFields) : Option BinaryRationalPairProgram.Source × ℕ :=
  checkWithWork parsed.lengthI parsed.lengthJ parsed.resourceI parsed.resourceJ
    parsed.lengthI_canonical parsed.lengthJ_canonical parsed.resourceI_canonical parsed.resourceJ_canonical

def setupWithWork (frame : List Bool) : Option (BinaryRationalPairProgram.Source × List Bool) × ℕ :=
  let parsed := readFieldsCertifiedWithWork frame
  match parsed.1 with
  | none => (none, parsed.2)
  | some fields =>
      let checked := parsedCheckWithWork fields
      (checked.1.map (fun source => (source, fields.suffix)), parsed.2 + checked.2)

theorem setupWithWork_bound (frame : List Bool) :
    (setupWithWork frame).2 ≤ 900 * (frame.length + 1) ^ 3 + 2000 * (frame.length + 2) ^ 2 + 8 := by
  have hp := readFieldsWithWork_bound frame
  rw [← readFieldsCertifiedWithWork_cost frame] at hp
  unfold setupWithWork
  dsimp only
  cases hParsed : (readFieldsCertifiedWithWork frame).1
  · dsimp only
    omega
  · rename_i fields
    have hs := readFieldsCertifiedWithWork_sizes frame fields hParsed
    have hCheck := checkWithWork_bound fields.lengthI fields.lengthJ fields.resourceI fields.resourceJ
      fields.lengthI_canonical fields.lengthJ_canonical fields.resourceI_canonical fields.resourceJ_canonical
      (frame.length + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hCheck' : (parsedCheckWithWork fields).2 ≤ 2000 * (frame.length + 2) ^ 2 + 8 := hCheck
    change (readFieldsCertifiedWithWork frame).2 + (parsedCheckWithWork fields).2 ≤ _
    omega

def ParsedFields.fields (parsed : ParsedFields) : SignedWord × SignedWord × SignedWord × SignedWord × List Bool :=
  (parsed.lengthI, parsed.lengthJ, parsed.resourceI, parsed.resourceJ, parsed.suffix)

theorem readFieldsCertifiedWithWork_state (frame : List Bool) :
    (readFieldsCertifiedWithWork frame).1.map ParsedFields.fields = BinaryRationalPairProgram.readFields frame := by
  unfold readFieldsCertifiedWithWork
  dsimp only
  split
  · rename_i h1
    rw [← readFieldsWithWork_state]
    simp only [readFieldsWithWork, h1, Option.map_none]
  · rename_i first h1
    split
    · rename_i h2
      rw [← readFieldsWithWork_state]
      simp only [readFieldsWithWork, h1, h2, Option.map_none]
    · rename_i second h2
      split
      · rename_i h3
        rw [← readFieldsWithWork_state]
        simp only [readFieldsWithWork, h1, h2, h3, Option.map_none]
      · rename_i third h3
        split <;> rw [← readFieldsWithWork_state]
        · rename_i h4
          simp only [readFieldsWithWork, h1, h2, h3, h4, Option.map_none]
        · rename_i fourth h4
          simp only [readFieldsWithWork, h1, h2, h3, h4, Option.map_some, ParsedFields.fields]

theorem setupWithWork_failure_of_parse (frame : List Bool) (h : BinaryRationalPairProgram.readFields frame = none) :
    (setupWithWork frame).1 = none := by
  have hs := readFieldsCertifiedWithWork_state frame
  rw [h] at hs
  have hNone : (readFieldsCertifiedWithWork frame).1 = none := by
    cases hp : (readFieldsCertifiedWithWork frame).1
    · rfl
    · rw [hp, Option.map_some] at hs
      cases hs
  unfold setupWithWork
  dsimp only
  rw [hNone]

theorem readFieldsCertifiedWithWork_complete (frame : List Bool) (lengthI lengthJ resourceI resourceJ : SignedWord)
    (suffix : List Bool)
    (h : BinaryRationalPairProgram.readFields frame = some (lengthI, lengthJ, resourceI, resourceJ, suffix)) :
    ∃ parsed, (readFieldsCertifiedWithWork frame).1 = some parsed ∧
      parsed.fields = (lengthI, lengthJ, resourceI, resourceJ, suffix) := by
  have he := readFieldsCertifiedWithWork_state frame
  rw [h] at he
  cases hp : (readFieldsCertifiedWithWork frame).1
  · rw [hp, Option.map_none] at he
    cases he
  · rename_i parsed
    rw [hp, Option.map_some] at he
    exact ⟨parsed, rfl, Option.some.inj he⟩

theorem checkedSource_fields (parsed : ParsedFields) (source : BinaryRationalPairProgram.Source)
    (h : (parsedCheckWithWork parsed).1 = some source) :
    source.lengthI = parsed.lengthI ∧ source.lengthJ = parsed.lengthJ ∧
      source.resourceI = parsed.resourceI ∧ source.resourceJ = parsed.resourceJ := by
  unfold parsedCheckWithWork checkWithWork BinaryRationalPairProgram.fromCanonicalChecked at h
  dsimp only at h
  split at h
  · split at h
    · cases Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem setupWithWork_sound (frame : List Bool) (source : BinaryRationalPairProgram.Source) (suffix : List Bool)
    (h : (setupWithWork frame).1 = some (source, suffix)) :
    BinaryRationalPairProgram.readFields frame = some (source.lengthI, source.lengthJ, source.resourceI, source.resourceJ, suffix) := by
  unfold setupWithWork at h
  dsimp only at h
  cases hParsed : (readFieldsCertifiedWithWork frame).1
  · rw [hParsed] at h
    cases h
  · rename_i parsed
    rw [hParsed] at h
    dsimp only at h
    cases hCheck : (parsedCheckWithWork parsed).1
    · rw [hCheck, Option.map_none] at h
      cases h
    · rename_i checked
      rw [hCheck, Option.map_some] at h
      have hp := Option.some.inj h
      have hSource : checked = source := congrArg Prod.fst hp
      have hSuffix : parsed.suffix = suffix := congrArg Prod.snd hp
      subst checked
      have hFields := checkedSource_fields parsed source hCheck
      have hs := readFieldsCertifiedWithWork_state frame
      rw [hParsed, Option.map_some] at hs
      rw [← hs]
      simp only [ParsedFields.fields, hFields.1, hFields.2.1, hFields.2.2.1, hFields.2.2.2, hSuffix]

theorem setupWithWork_encoded_complete (pair : RationalRoundingPair) (suffix : List Bool) :
    ∃ source, (setupWithWork (BinaryRationalPairProgram.encodedFields pair ++ suffix)).1 = some (source, suffix) ∧
      source.pair = pair := by
  obtain ⟨lengthI, lengthJ, resourceI, resourceJ, hRead, vLI, vLJ, vRI, vRJ, cLI, cLJ, cRI, cRJ⟩ :=
    BinaryRationalPairProgram.readFields_encode_append pair suffix
  obtain ⟨parsed, hParsed, hFields⟩ := readFieldsCertifiedWithWork_complete _ _ _ _ _ _ hRead
  have hLI : parsed.lengthI = lengthI := congrArg Prod.fst hFields
  have hLJ : parsed.lengthJ = lengthJ := congrArg (fun p => p.2.1) hFields
  have hRI : parsed.resourceI = resourceI := congrArg (fun p => p.2.2.1) hFields
  have hRJ : parsed.resourceJ = resourceJ := congrArg (fun p => p.2.2.2.1) hFields
  have hSuffix : parsed.suffix = suffix := congrArg (fun p => p.2.2.2.2) hFields
  have hI : 0 < value parsed.resourceI ∧ value parsed.resourceI < value parsed.lengthI := by
    rw [hRI, hLI, vRI, vLI]
    exact pair.interiorI
  have hJ : 0 < value parsed.resourceJ ∧ value parsed.resourceJ < value parsed.lengthJ := by
    rw [hRJ, hLJ, vRJ, vLJ]
    exact pair.interiorJ
  obtain ⟨source, hCheck, hSLI, hSLJ, hSRI, hSRJ⟩ := BinaryRationalPairProgram.fromCanonicalChecked_complete
    parsed.lengthI parsed.lengthJ parsed.resourceI parsed.resourceJ parsed.lengthI_canonical parsed.lengthJ_canonical
    parsed.resourceI_canonical parsed.resourceJ_canonical hI hJ
  refine ⟨source, ?_, ?_⟩
  · unfold setupWithWork
    dsimp only
    rw [hParsed]
    change ((parsedCheckWithWork parsed).1.map (fun source => (source, parsed.suffix))) = _
    change BinaryRationalPairProgram.fromCanonicalChecked _ _ _ _ _ _ _ _ = some source at hCheck
    rw [show (parsedCheckWithWork parsed).1 = some source from hCheck, Option.map_some, hSuffix]
  · have hData : source.pair.lengthI = pair.lengthI ∧ source.pair.lengthJ = pair.lengthJ ∧
        source.pair.resourceI = pair.resourceI ∧ source.pair.resourceJ = pair.resourceJ := by
      simp [BinaryRationalPairProgram.Source.pair, hSLI, hSLJ, hSRI, hSRJ, hLI, hLJ, hRI, hRJ, vLI, vLJ, vRI, vRJ]
    have hEq : ∀ a b : RationalRoundingPair,
        a.lengthI = b.lengthI → a.lengthJ = b.lengthJ → a.resourceI = b.resourceI → a.resourceJ = b.resourceJ → a = b := by
      intro a b h1 h2 h3 h4
      cases a
      cases b
      simp only at h1 h2 h3 h4
      cases h1
      cases h2
      cases h3
      cases h4
      rfl
    exact hEq source.pair pair hData.1 hData.2.1 hData.2.2.1 hData.2.2.2

def preparePairWithWork (frame : List Bool) : Option (Array SignedWord × List Bool) × ℕ :=
  let setup := setupWithWork frame
  match setup.1 with
  | none => (none, setup.2)
  | some parsed =>
      let result := parsed.1.runWithWork
      (some (result.1, parsed.2), setup.2 + parsed.1.sourcePayloadWork + result.2)

theorem preparePairWithWork_success (frame : List Bool) (source : BinaryRationalPairProgram.Source) (suffix : List Bool)
    (h : (setupWithWork frame).1 = some (source, suffix)) :
    (preparePairWithWork frame).1 = some (source.run, suffix) := by
  unfold preparePairWithWork
  dsimp only
  rw [h]
  dsimp only
  rw [BinaryRationalPairProgram.Source.runWithWork, BinaryRationalRegisterProgram.runWithWork_refines]
  rfl

theorem preparePairWithWork_bound (frame : List Bool) (source : BinaryRationalPairProgram.Source) (suffix : List Bool)
    (hParsed : (setupWithWork frame).1 = some (source, suffix)) {s : ℕ}
    (hHeight : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    (preparePairWithWork frame).2 ≤
      900 * (frame.length + 1) ^ 3 + 2000 * (frame.length + 2) ^ 2 + 8 +
        (8 * (3 + 4 * s) + 4 + 7 * (12000 * (32 * s + 32) ^ 3 + 28 * (64 * s + 63) + 4)) := by
  have hSetup := setupWithWork_bound frame
  have hRun := source.preparationWork_bound hHeight hs
  unfold preparePairWithWork
  dsimp only
  rw [hParsed]
  change (setupWithWork frame).2 + source.sourcePayloadWork + source.runWithWork.2 ≤ _
  change source.sourcePayloadWork + source.runWithWork.2 ≤ _ at hRun
  omega

theorem preparePairWithWork_lattice_bound (frame : List Bool) (source : BinaryRationalPairProgram.Source) (suffix : List Bool)
    (hParsed : (setupWithWork frame).1 = some (source, suffix)) {D : ℕ}
    (hD : 0 < D) (hLattice : source.pair.Lattice D)
    (hLI : source.pair.lengthI ≤ 1) (hLJ : source.pair.lengthJ ≤ 1) :
    (preparePairWithWork frame).2 ≤
      900 * (frame.length + 1) ^ 3 + 2000 * (frame.length + 2) ^ 2 + 8 +
        (8 * (11 + 4 * binaryWordWidth D) + 4 +
          7 * (12000 * (32 * binaryWordWidth D + 96) ^ 3 + 28 * (64 * binaryWordWidth D + 191) + 4)) := by
  have h := preparePairWithWork_bound frame source suffix hParsed
    (RationalPairProgram.fieldsHeight_lattice source.pair hD hLattice hLI hLJ) (by omega)
  have hPayload : 3 + 4 * (2 + binaryWordWidth D) = 11 + 4 * binaryWordWidth D := by omega
  have hWidth : 32 * (2 + binaryWordWidth D) + 32 = 32 * binaryWordWidth D + 96 := by omega
  have hFields : 64 * (2 + binaryWordWidth D) + 63 = 64 * binaryWordWidth D + 191 := by omega
  rw [hPayload, hWidth, hFields] at h
  exact h

end Blotto.BinaryRationalSetupWork
