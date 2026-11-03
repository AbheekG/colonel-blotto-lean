import Blotto.BinaryRationalSetupWork
import Blotto.BinaryOverlapWorkspaceJoin

/-! An actual sixteen-signed-frame reader prepares the stored Boolean overlap
environment. It preserves the retained rational frame semantics and suffix,
rejects malformed or zero-denominator frames, and derives canonical words and
the preparation price from the incoming bit-list length. Encoding rational
source data below specifies the wire format only; the runtime parser never
calls that encoder or converts represented Rat/Nat values to Boolean words.
Source-controller field extraction and physical allocator/GC remain separate. -/

namespace Blotto.BinaryOverlapInputPreparation
open BinaryRationalNormalization BinaryRationalEncoding

def readWordsWithWork : ℕ → List Bool → Option (List SignedWord × List Bool) × ℕ
  | 0, frame => (some ([], frame), 1)
  | count + 1, frame =>
      let first := BinaryRationalSetupWork.readFrameWithWork frame
      match first.1 with
      | none => (none, first.2 + 2)
      | some parsed =>
          let later := readWordsWithWork count parsed.2
          (later.1.map (fun rest => (parsed.1 :: rest.1, rest.2)), first.2 + later.2 + 3)

def readRationals : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, frame => some ([], frame)
  | count + 1, frame =>
      (BinaryRatFrame.read frame).bind (fun first =>
        (readRationals count first.2).map (fun rest => (first.1 :: rest.1, rest.2)))

theorem readWordsWithWork_length (count : ℕ) (frame : List Bool) (words : List SignedWord) (suffix : List Bool)
    (h : (readWordsWithWork count frame).1 = some (words, suffix)) : words.length = count := by
  induction count generalizing frame words suffix with
  | zero => cases Option.some.inj h; rfl
  | succ count ih =>
      unfold readWordsWithWork at h
      dsimp only at h
      cases hf : (BinaryRationalSetupWork.readFrameWithWork frame).1 with
      | none => rw [hf] at h; cases h
      | some first =>
          rw [hf] at h
          dsimp only at h
          cases ht : (readWordsWithWork count first.2).1 with
          | none => rw [ht, Option.map_none] at h; cases h
          | some rest =>
              rw [ht, Option.map_some] at h
              cases Option.some.inj h
              simp only [List.length_cons, ih first.2 rest.1 rest.2 ht]

theorem readWordsWithWork_canonical (count : ℕ) (frame : List Bool) (words : List SignedWord) (suffix : List Bool)
    (h : (readWordsWithWork count frame).1 = some (words, suffix)) : ∀ word ∈ words, CanonicalWord word := by
  induction count generalizing frame words suffix with
  | zero => cases Option.some.inj h; simp
  | succ count ih =>
      unfold readWordsWithWork at h
      dsimp only at h
      cases hf : (BinaryRationalSetupWork.readFrameWithWork frame).1 with
      | none => rw [hf] at h; cases h
      | some first =>
          rw [hf] at h
          dsimp only at h
          cases ht : (readWordsWithWork count first.2).1 with
          | none => rw [ht, Option.map_none] at h; cases h
          | some rest =>
              rw [ht, Option.map_some] at h
              cases Option.some.inj h
              intro word hw
              rcases List.mem_cons.mp hw with hw | hw
              · subst word
                apply readFrame_canonical frame first.1 first.2
                rw [← BinaryRationalSetupWork.readFrameWithWork_state]
                exact hf
              · exact ih first.2 rest.1 rest.2 ht word hw

theorem readWordsWithWork_suffix (count : ℕ) (frame : List Bool) (words : List SignedWord) (suffix : List Bool)
    (h : (readWordsWithWork count frame).1 = some (words, suffix)) : suffix.length ≤ frame.length := by
  induction count generalizing frame words suffix with
  | zero => cases Option.some.inj h; exact le_rfl
  | succ count ih =>
      unfold readWordsWithWork at h
      dsimp only at h
      cases hf : (BinaryRationalSetupWork.readFrameWithWork frame).1 with
      | none => rw [hf] at h; cases h
      | some first =>
          rw [hf] at h
          dsimp only at h
          have hFirst : readFrame frame = some (first.1, first.2) := by
            rw [← BinaryRationalSetupWork.readFrameWithWork_state]; exact hf
          have hs := (BinaryRationalSetupWork.readFrame_sizes frame first.1 first.2 hFirst).2
          cases ht : (readWordsWithWork count first.2).1 with
          | none => rw [ht, Option.map_none] at h; cases h
          | some rest =>
              rw [ht, Option.map_some] at h
              cases Option.some.inj h
              exact (ih first.2 rest.1 rest.2 ht).trans hs

theorem readWordsWithWork_bound (count : ℕ) (frame : List Bool) :
    (readWordsWithWork count frame).2 ≤ 1 + count * (225 * (frame.length + 1) ^ 3) := by
  induction count generalizing frame with
  | zero => simp [readWordsWithWork]
  | succ count ih =>
      have hfW := BinaryRationalSetupWork.readFrameWithWork_bound frame
      have hp : 1 ≤ (frame.length + 1) ^ 3 := one_le_pow₀ (by omega)
      unfold readWordsWithWork
      dsimp only
      cases hf : (BinaryRationalSetupWork.readFrameWithWork frame).1 with
      | none => dsimp only; nlinarith
      | some first =>
          have hFirst : readFrame frame = some (first.1, first.2) := by
            rw [← BinaryRationalSetupWork.readFrameWithWork_state]; exact hf
          have hs := (BinaryRationalSetupWork.readFrame_sizes frame first.1 first.2 hFirst).2
          have ht := (ih first.2).trans (Nat.add_le_add_left
            (Nat.mul_le_mul_left count (Nat.mul_le_mul_left 225 (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 3))) 1)
          dsimp only
          nlinarith

theorem readWordsWithWork_refines (count : ℕ) (frame : List Bool) :
    (readWordsWithWork count frame).1.map (fun parsed => (parsed.1.map value, parsed.2)) = readRationals count frame := by
  induction count generalizing frame with
  | zero => rfl
  | succ count ih =>
      unfold readWordsWithWork readRationals
      dsimp only
      have hf := readFrame_refines frame
      rw [← BinaryRationalSetupWork.readFrameWithWork_state] at hf
      cases hp : (BinaryRationalSetupWork.readFrameWithWork frame).1 with
      | none => rw [hp, Option.map_none] at hf; rw [← hf]; rfl
      | some first =>
          rw [hp, Option.map_some] at hf
          rw [← hf, Option.bind_some]
          dsimp only
          rw [← ih first.2]
          cases ht : (readWordsWithWork count first.2).1 <;> simp [List.map_cons]

def encodeValues : List ℚ → List Bool
  | [] => []
  | q :: rest => BinaryRatFrame.encode q ++ encodeValues rest

theorem readRationals_encoded (values : List ℚ) (suffix : List Bool) :
    readRationals values.length (encodeValues values ++ suffix) = some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons q rest ih => simp only [List.length_cons, encodeValues, List.append_assoc, readRationals,
      BinaryRatFrame.read_encode_append, Option.bind_some, ih, Option.map_some]

theorem readWordsWithWork_complete (count : ℕ) (frame : List Bool) (values : List ℚ) (suffix : List Bool)
    (h : readRationals count frame = some (values, suffix)) :
    ∃ words, (readWordsWithWork count frame).1 = some (words, suffix) ∧ words.map value = values := by
  have he := readWordsWithWork_refines count frame
  rw [h] at he
  cases hp : (readWordsWithWork count frame).1 with
  | none => rw [hp, Option.map_none] at he; cases he
  | some parsed =>
      rw [hp, Option.map_some] at he
      have hValues := congrArg Prod.fst (Option.some.inj he)
      have hSuffix := congrArg Prod.snd (Option.some.inj he)
      rcases parsed with ⟨words, tail⟩
      dsimp only at hValues hSuffix
      subst tail
      exact ⟨words, rfl, hValues⟩

def wordsTable (words : List SignedWord) {n : ℕ} (h : words.length = n) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => words[j.val]'(by rw [h]; exact j.isLt))

theorem table_ext {n : ℕ} {α : Type*} (first second : FixedArrayTable n α)
    (h : ∀ j, first.read j = second.read j) : first = second := by
  cases first with
  | mk a ha =>
    cases second with
    | mk b hb =>
      have he : a = b := by
        apply Array.ext
        · omega
        · intro r hr ht
          have hn : r < n := by omega
          exact h ⟨r, hn⟩
      subst b
      rfl

theorem wordsTable_interpreted (words : List SignedWord) {n : ℕ} (h : words.length = n)
    (qenv : FixedArrayTable n ℚ) (hv : words.map value = List.ofFn qenv.read) :
    BinaryRationalExpression.interpretedEnvironment (wordsTable words h) = qenv := by
  have hRead : ∀ j, (BinaryRationalExpression.interpretedEnvironment (wordsTable words h)).read j = qenv.read j := by
    intro j
    have hGet := congrArg (fun list : List ℚ => list[j.val]?) hv
    simp only [List.getElem?_map, List.getElem?_ofFn] at hGet
    have hWord : j.val < words.length := by omega
    rw [List.getElem?_eq_getElem hWord, dite_eq_left j.isLt] at hGet
    simp only [Option.map_some] at hGet
    have hVal := Option.some.inj hGet
    simpa only [BinaryRationalExpression.interpretedEnvironment, wordsTable,
      FixedArrayTable.read_ofFn] using hVal
  exact table_ext _ _ hRead

def prepareWithWork (frame : List Bool) : Option (FixedArrayTable 16 SignedWord × List Bool) × ℕ :=
  let parsed := readWordsWithWork 16 frame
  match h : parsed.1 with
  | none => (none, parsed.2)
  | some result =>
      let table := wordsTable result.1 (readWordsWithWork_length 16 frame result.1 result.2 h)
      (some (table, result.2), parsed.2 + 16 * (2 * frame.length + 3) + 4)

theorem prepareWithWork_success (frame : List Bool) (words : List SignedWord) (suffix : List Bool)
    (h : (readWordsWithWork 16 frame).1 = some (words, suffix)) :
    (prepareWithWork frame).1 = some (wordsTable words (readWordsWithWork_length _ _ _ _ h), suffix) := by
  unfold prepareWithWork
  dsimp only
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i parsed hp
    have he : parsed = (words, suffix) := Option.some.inj (hp.symm.trans h)
    subst parsed
    rfl

theorem prepareWithWork_failure_iff (frame : List Bool) :
    (prepareWithWork frame).1 = none ↔ readRationals 16 frame = none := by
  have href := readWordsWithWork_refines 16 frame
  have hp : (prepareWithWork frame).1 = none ↔ (readWordsWithWork 16 frame).1 = none := by
    unfold prepareWithWork
    dsimp only
    split
    · rename_i hn
      simp [hn]
    · rename_i parsed hp
      simp [hp]
  rw [hp, ← href]
  cases h : (readWordsWithWork 16 frame).1 <;> simp

theorem readWordsWithWork_first_failure (count : ℕ) (frame : List Bool)
    (h : BinaryRatFrame.read frame = none) : (readWordsWithWork (count + 1) frame).1 = none := by
  have hf := readFrame_refines frame
  rw [h, ← BinaryRationalSetupWork.readFrameWithWork_state] at hf
  have hn : (BinaryRationalSetupWork.readFrameWithWork frame).1 = none := by
    cases he : (BinaryRationalSetupWork.readFrameWithWork frame).1 <;> simp_all
  simp only [readWordsWithWork, hn]

theorem prepareWithWork_empty : (prepareWithWork []).1 = none := by
  rw [prepareWithWork_failure_iff]
  rfl

theorem prepareWithWork_zero_denominator (negative : Bool) (magnitude : ℕ) (suffix : List Bool) :
    (prepareWithWork (negative :: (BinaryNatFrame.encode magnitude ++ BinaryNatFrame.encode 0 ++ suffix))).1 = none := by
  rw [prepareWithWork_failure_iff]
  simp only [readRationals, BinaryRatFrame.read_zero_denominator, Option.bind_none]

theorem prepareWithWork_semantics (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (h : (prepareWithWork frame).1 = some (env, suffix)) :
    readRationals 16 frame = some (List.ofFn (fun j => value (env.read j)), suffix) := by
  unfold prepareWithWork at h
  dsimp only at h
  split at h
  · cases h
  · rename_i parsed hp
    cases Option.some.inj h
    have he := readWordsWithWork_refines 16 frame
    rw [hp, Option.map_some] at he
    rw [← he]
    congr 1
    congr 1
    apply List.ext_getElem
    · simp [List.length_map, readWordsWithWork_length _ _ _ _ hp]
    · intro r hr hs
      simp only [List.getElem_map, List.getElem_ofFn, wordsTable, FixedArrayTable.read_ofFn]

theorem prepareWithWork_interpreted (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (qenv : FixedArrayTable 16 ℚ) (h : (prepareWithWork frame).1 = some (env, suffix))
    (hWire : readRationals 16 frame = some (List.ofFn qenv.read, suffix)) :
    BinaryRationalExpression.interpretedEnvironment env = qenv := by
  have he := prepareWithWork_semantics frame env suffix h
  rw [hWire] at he
  have hList := congrArg Prod.fst (Option.some.inj he)
  apply table_ext
  intro r
  have hGet := congrArg (fun list : List ℚ => list[r.val]?) hList
  simp only [List.getElem?_ofFn, r.isLt, dite_true] at hGet
  have hVal := (Option.some.inj hGet).symm
  simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hVal

theorem prepareWithWork_canonical (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (h : (prepareWithWork frame).1 = some (env, suffix)) : ∀ j, CanonicalWord (env.read j) := by
  unfold prepareWithWork at h
  dsimp only at h
  split at h
  · cases h
  · rename_i parsed hp
    cases Option.some.inj h
    intro j
    rw [wordsTable, FixedArrayTable.read_ofFn]
    exact readWordsWithWork_canonical 16 frame parsed.1 parsed.2 hp _ (List.getElem_mem _)

theorem prepareWithWork_bound (frame : List Bool) :
    (prepareWithWork frame).2 ≤ 4000 * (frame.length + 1) ^ 3 := by
  have hp := readWordsWithWork_bound 16 frame
  have hl : frame.length + 1 ≤ (frame.length + 1) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < frame.length + 1) (by omega : 1 ≤ 3))
  unfold prepareWithWork
  dsimp only
  split <;> nlinarith

def encodedEnvironment {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) : List Bool :=
  encodeValues (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r))

theorem prepareWithWork_encoded {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (suffix : List Bool) :
    ∃ env, (prepareWithWork (encodedEnvironment G B i j ++ suffix)).1 = some (env, suffix) ∧
      BinaryRationalExpression.interpretedEnvironment env = RationalOverlapFormula.environment G B i j := by
  let values := List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r)
  have hLength : values.length = 16 := by simp [values]
  have hRead := readRationals_encoded values suffix
  rw [hLength] at hRead
  obtain ⟨words, hp, hv⟩ := readWordsWithWork_complete 16 (encodeValues values ++ suffix) values suffix hRead
  have hw := readWordsWithWork_length 16 (encodeValues values ++ suffix) words suffix hp
  let env := wordsTable words hw
  refine ⟨env, ?_, ?_⟩
  · exact prepareWithWork_success _ words suffix hp
  · exact wordsTable_interpreted words hw _ hv

def evaluationWorkBound (s : ℕ) : ℕ :=
  128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 7) +
    8 * (256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9))

def prepareAndEvaluateWithWork (frame : List Bool) :
    Option (SignedWord × FixedArrayTable 4 SignedWord × FixedArrayTable 4 SignedWord × List Bool) × ℕ :=
  let parsed := prepareWithWork frame
  match parsed.1 with
  | none => (none, parsed.2)
  | some prepared =>
      let w := BinaryOverlapCompilerBridge.weight.compile.run prepared.1
      let p := FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeP r).compile.run prepared.1).1)
      let q := FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeQ r).compile.run prepared.1).1)
      (some (w.1, p, q, prepared.2), parsed.2 +
        BinaryOverlapCompilerBridge.weight.compile.bitWork prepared.1 +
        (List.ofFn (fun r => (BinaryOverlapCompilerBridge.safeP r).compile.bitWork prepared.1)).sum +
        (List.ofFn (fun r => (BinaryOverlapCompilerBridge.safeQ r).compile.bitWork prepared.1)).sum +
        -- AST emission, two output tables, and result packaging.
        768 + 8 * 1536 + 32)

theorem prepareAndEvaluateWithWork_state (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (h : (prepareWithWork frame).1 = some (env, suffix)) :
    (prepareAndEvaluateWithWork frame).1 = some
      ((BinaryOverlapCompilerBridge.weight.compile.run env).1,
        FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeP r).compile.run env).1),
        FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeQ r).compile.run env).1), suffix) := by
  unfold prepareAndEvaluateWithWork
  dsimp only
  rw [h]

theorem prepareAndEvaluateWithWork_values {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (hParsed : (prepareWithWork frame).1 = some (env, suffix))
    (hWire : readRationals 16 frame = some
      (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r), suffix)) :
    ∃ weight p q, (prepareAndEvaluateWithWork frame).1 = some (weight, p, q, suffix) ∧
      value weight = G.weight i j ∧ (∀ r, value (p.read r) = G.safeP B i j r) ∧
      (∀ r, value (q.read r) = G.safeQ B i j r) := by
  have hc := prepareWithWork_canonical frame env suffix hParsed
  have hi := prepareWithWork_interpreted frame env suffix _ hParsed hWire
  have hv := BinaryOverlapCompilerBridge.gluing_values G B i j env (fun r => (hc r).1) hi
  refine ⟨_, _, _, prepareAndEvaluateWithWork_state frame env suffix hParsed, hv.1, ?_, ?_⟩
  · intro r
    simpa only [FixedArrayTable.read_ofFn] using hv.2.1 r
  · intro r
    simpa only [FixedArrayTable.read_ofFn] using hv.2.2 r

theorem parsed_gluing_contract {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (hParsed : (prepareWithWork frame).1 = some (env, suffix))
    (hWire : readRationals 16 frame = some
      (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r), suffix))
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    value (BinaryOverlapCompilerBridge.weight.compile.runWithWorkspace env).1.1 = G.weight i j ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeP r).compile.runWithWorkspace env).1.1 = G.safeP B i j r) ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeQ r).compile.runWithWorkspace env).1.1 = G.safeQ B i j r) ∧
      BinaryOverlapCompilerBridge.weight.compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.weightStorageBound s ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeP r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeQ r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) := by
  have hCanonical := prepareWithWork_canonical frame env suffix hParsed
  have hInputs := prepareWithWork_interpreted frame env suffix _ hParsed hWire
  exact BinaryOverlapCompilerBridge.gluing_workspace_contract G B i j env hCanonical hInputs s hs hFirst hSecond hD hB

theorem prepareAndEvaluateWithWork_bound {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (frame : List Bool) (env : FixedArrayTable 16 SignedWord) (suffix : List Bool)
    (hParsed : (prepareWithWork frame).1 = some (env, suffix))
    (hWire : readRationals 16 frame = some
      (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r), suffix))
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    (prepareAndEvaluateWithWork frame).2 ≤ 4000 * (frame.length + 1) ^ 3 + evaluationWorkBound s + 13088 := by
  have hp := prepareWithWork_bound frame
  have hCanonical := prepareWithWork_canonical frame env suffix hParsed
  have hInputs := prepareWithWork_interpreted frame env suffix _ hParsed hWire
  have hHeight : ∀ r, RationalHeight (value (env.read r)) s := by
    intro r
    have hh := RationalOverlapFormula.environment_height G B i j s hFirst hSecond hD hB r
    rw [← hInputs] at hh
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hh
  have hc := BinaryOverlapCompilerBridge.compiled_bitWork env hCanonical s hs hHeight
  have hP : (List.ofFn (fun r => (BinaryOverlapCompilerBridge.safeP r).compile.bitWork env)).sum ≤
      4 * (256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) := by
    rw [List.sum_ofFn]
    exact (Finset.sum_le_sum (fun r _ => hc.2.1 r)).trans_eq (by simp)
  have hQ : (List.ofFn (fun r => (BinaryOverlapCompilerBridge.safeQ r).compile.bitWork env)).sum ≤
      4 * (256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) := by
    rw [List.sum_ofFn]
    exact (Finset.sum_le_sum (fun r _ => hc.2.2 r)).trans_eq (by simp)
  unfold prepareAndEvaluateWithWork
  dsimp only
  rw [hParsed]
  dsimp only
  unfold evaluationWorkBound
  omega

theorem encoded_gluing_preparation_contract {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ)
    (i : Fin k) (j : Fin h) (suffix : List Bool) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    ∃ env,
      (prepareWithWork (encodedEnvironment G B i j ++ suffix)).1 = some (env, suffix) ∧
      (∀ r, CanonicalWord (env.read r)) ∧
      BinaryRationalExpression.interpretedEnvironment env = RationalOverlapFormula.environment G B i j ∧
      value (BinaryOverlapCompilerBridge.weight.compile.runWithWorkspace env).1.1 = G.weight i j ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeP r).compile.runWithWorkspace env).1.1 = G.safeP B i j r) ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeQ r).compile.runWithWorkspace env).1.1 = G.safeQ B i j r) ∧
      (prepareWithWork (encodedEnvironment G B i j ++ suffix)).2 ≤
        4000 * ((encodedEnvironment G B i j ++ suffix).length + 1) ^ 3 ∧
      (prepareAndEvaluateWithWork (encodedEnvironment G B i j ++ suffix)).2 ≤
        4000 * ((encodedEnvironment G B i j ++ suffix).length + 1) ^ 3 + evaluationWorkBound s + 13088 ∧
      BinaryOverlapCompilerBridge.weight.compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.weightStorageBound s ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeP r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeQ r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) := by
  obtain ⟨env, hp, hi⟩ := prepareWithWork_encoded G B i j suffix
  have hc := prepareWithWork_canonical _ env suffix hp
  have hLength : (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r)).length = 16 := by simp
  have hw := readRationals_encoded (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r)) suffix
  rw [hLength] at hw
  have hWire : readRationals 16 (encodedEnvironment G B i j ++ suffix) =
      some (List.ofFn (fun r => (RationalOverlapFormula.environment G B i j).read r), suffix) := hw
  have he := parsed_gluing_contract G B i j _ env suffix hp hWire s hs hFirst hSecond hD hB
  have ht := prepareAndEvaluateWithWork_bound G B i j _ env suffix hp hWire s hs hFirst hSecond hD hB
  exact ⟨env, hp, hc, hi, he.1, he.2.1, he.2.2.1, prepareWithWork_bound _, ht,
    he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩

end Blotto.BinaryOverlapInputPreparation
