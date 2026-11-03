import Blotto.BinarySeedLookupTree
import Blotto.BinaryIndexWord
import Blotto.BinaryStoredCoinIndexedWork

/-! The stored coin controller retains its program counter as a Boolean word.
Its native guard, seed read and increment use the concrete prepared seed store.
Natural values, ofNat and subtraction occur in proof indices, termination and
refinement specifications; they do not control the native reader/index path.
The joined ledger counts reached word/control/Boolean/list/tree components.
Pointer widths, object layout, ownership and complete physical execution remain
separate obligations. -/

namespace Blotto.BinaryWordIndexCoinController
open BinarySeedLookupTree

theorem word_ext {width : ℕ} (first second : FixedBinaryWord width)
    (h : first.value = second.value) : first = second := by
  cases first with
  | mk fb hf =>
      cases second with
      | mk sb hs =>
          have he := BinaryBorrowWord.littleValue_injective fb sb (hf.trans hs.symm) h
          cases he
          rfl

/-- The cap word supplies a physical Boolean ruler for the initial counter. -/
def zeroIndex (store : Store) : FixedBinaryWord store.width :=
  ⟨store.cap.bits.map (fun _ => false),by simpa using store.cap.size⟩

theorem falseMap_value (bits : List Bool) :
    BinaryBigEndian.littleValue (bits.map (fun _ => false)) = 0 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [List.map_cons,BinaryBigEndian.littleValue,Bool.false_eq_true,ite_false,ih,Nat.mul_zero,Nat.zero_add]

theorem zeroIndex_value (store : Store) : (zeroIndex store).value = 0 :=
  falseMap_value store.cap.bits

/-- A natural-index reference reader, used only in specifications. -/
def reader (store : Store) (index : Fin store.cap.value) : Bool :=
  store.lookup (FixedBinaryWord.ofNat store.width index.val)

theorem lookup_reader (store : Store) (pc : FixedBinaryWord store.width)
    (hRead : pc.value < store.cap.value) :
    store.lookup pc = reader store ⟨pc.value,hRead⟩ := by
  have hw : FixedBinaryWord.ofNat store.width pc.value = pc := by
    apply word_ext
    exact FixedBinaryWord.value_ofNat _ _ (hRead.trans store.cap_room)
  unfold reader
  rw [hw]

theorem reader_prepare (seed : List Bool) (index : Fin (prepare seed).cap.value) :
    reader (prepare seed) index = seed.getD index.val false := by
  unfold reader
  rw [prepare_lookup,FixedBinaryWord.value_ofNat _ _ (index.isLt.trans (prepare seed).cap_room)]

theorem guard_value (store : Store) (pc : FixedBinaryWord store.width) :
    (BinaryIndexWord.ltWithWork pc store.cap).1 = true ↔ pc.value < store.cap.value :=
  BinaryIndexWord.lt_value pc store.cap

theorem advance_value (store : Store) (pc : FixedBinaryWord store.width)
    (hRead : (BinaryIndexWord.ltWithWork pc store.cap).1 = true) :
    (BinaryIndexWord.incrementWithWork pc).1.1.value = pc.value + 1 := by
  have hr := (guard_value store pc).mp hRead
  have hRoom : pc.value + 1 < 2 ^ store.width := by
    have hc := store.cap_room
    omega
  exact (BinaryIndexWord.increment_value pc hRoom).1

theorem advance_bound (store : Store) (pc : FixedBinaryWord store.width)
    (hRead : (BinaryIndexWord.ltWithWork pc store.cap).1 = true) :
    (BinaryIndexWord.incrementWithWork pc).1.1.value ≤ store.cap.value := by
  rw [advance_value store pc hRead]
  exact Nat.succ_le_of_lt ((guard_value store pc).mp hRead)

abbrev Result (store : Store) := (Option Bool × FixedBinaryWord store.width) × ℕ

/-- One actual source read and one fixed-width increment on each pending read.
The two body labels retain the original zero/one/mismatch/exhaustion control
allowance; reached comparison/read/increment components are added separately. -/
def run {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) : Result store :=
  let body := FixedWordCoin.bodyWork a b + 2
  if a.isZero then ((some false,pc),body) else if a.same b then ((some true,pc),body) else
    let guard := BinaryIndexWord.ltWithWork pc store.cap
    if hRead : guard.1 = true then
      let read := store.lookupWithVisits pc
      let next := a.coinStep b
      let advanced := BinaryIndexWord.incrementWithWork pc
      let stepCharge := body + guard.2 + read.2 + advanced.2
      if read.1 = next.1 then
        let later := run store next.2 b advanced.1.1 (advance_bound store pc hRead)
        (later.1,stepCharge + later.2)
      else ((some (!read.1),advanced.1.1),stepCharge)
    else ((none,pc),body + guard.2)
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (guard_value store pc).mp hRead
  have hn := advance_value store pc hRead
  omega

/-- Decode only the retained result counter in the refinement specification. -/
def decoded (store : Store) (result : Result store) : Option Bool × ℕ :=
  (result.1.1,result.1.2.value)

theorem run_state {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (run store a b pc hp) =
      BinaryStoredCoinIndexed.run store.cap.value (reader store) a b pc.value hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  by_cases hz : a.isZero = true
  · simp only [hz,ite_true,decoded]
  · simp only [hz,Bool.false_eq_true,ite_false]
    by_cases he : a.same b = true
    · simp only [he,ite_true,decoded]
    · simp only [he,Bool.false_eq_true,ite_false]
      by_cases hr : pc.value < store.cap.value
      · have hg := (guard_value store pc).mpr hr
        simp only [hg,dite_eq_left,dite_eq_left hr]
        have hRead := lookup_reader store pc hr
        have hn := advance_value store pc hg
        simp only [Store.lookupWithVisits,hRead]
        by_cases hd : reader store ⟨pc.value,hr⟩ = (a.coinStep b).1
        · simp only [hd,ite_true]
          have ih := run_state store (a.coinStep b).2 b
            (BinaryIndexWord.incrementWithWork pc).1.1 (advance_bound store pc hg)
          simpa only [decoded,hn] using ih
        · simp only [hd,ite_false,decoded,hn]
      · have hg : (BinaryIndexWord.ltWithWork pc store.cap).1 ≠ true := by
          intro h
          exact hr ((guard_value store pc).mp h)
        simp only [hg,Bool.false_eq_true,dite_false,dite_eq_right hr,decoded]
termination_by store.cap.value - pc.value
decreasing_by
  have _hn := advance_value store pc ((guard_value store pc).mpr hr)
  omega

/-- The per-visit allowance is derived from reached word, guard, reader and
increment primitives. No external backend price is assumed. -/
def allowance (width indexWidth : ℕ) : ℕ := 24 * width + 30 + 20 * indexWidth + 20

theorem body_bound {width : ℕ} (a b : FixedBinaryWord width) :
    FixedWordCoin.bodyWork a b + 2 ≤ 24 * width + 30 := by
  have h := FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at h
  omega

theorem local_bound {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) :
    FixedWordCoin.bodyWork a b + 2 + (BinaryIndexWord.ltWithWork pc store.cap).2 +
      (store.lookupWithVisits pc).2 + (BinaryIndexWord.incrementWithWork pc).2 ≤
        allowance width store.width := by
  have hb := body_bound a b
  have hg := BinaryIndexWord.ltWithWork_bound pc store.cap
  have hi := BinaryIndexWord.incrementWithWork_bound pc
  have hr := store.lookupVisits_exact pc
  change (store.lookupWithVisits pc).2 = 2 * store.width + 1 at hr
  unfold allowance
  omega

theorem run_bound {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).2 ≤ allowance width store.width * (store.cap.value - pc.value + 1) := by
  have hb := body_bound a b
  have hg := BinaryIndexWord.ltWithWork_bound pc store.cap
  have hl := local_bound store a b pc
  have hOne : 1 ≤ store.cap.value - pc.value + 1 := by omega
  conv_lhs => unfold run
  dsimp only
  split_ifs with hz he hRead hd
  · unfold allowance
    nlinarith
  · unfold allowance
    nlinarith
  · have hn := advance_value store pc hRead
    have ih := run_bound store (a.coinStep b).2 b
      (BinaryIndexWord.incrementWithWork pc).1.1 (advance_bound store pc hRead)
    have hDepth : store.cap.value - pc.value + 1 =
        (store.cap.value - (BinaryIndexWord.incrementWithWork pc).1.1.value + 1) + 1 := by
      have hr := (guard_value store pc).mp hRead
      omega
    rw [hDepth]
    nlinarith
  · exact hl.trans (Nat.le_mul_of_pos_right _ (by omega))
  · unfold allowance
    nlinarith
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (guard_value store pc).mp hRead
  have _hn := advance_value store pc hRead
  omega


theorem run_result {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).1.1 =
      (BinaryStoredCoinIndexed.run store.cap.value (reader store) a b pc.value hp).1 :=
  congrArg Prod.fst (run_state store a b pc hp)

theorem run_final_position {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).1.2.value =
      (BinaryStoredCoinIndexed.run store.cap.value (reader store) a b pc.value hp).2 :=
  congrArg Prod.snd (run_state store a b pc hp)

theorem run_position_bounds {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store a b pc hp).1.2.value ∧
      (run store a b pc hp).1.2.value ≤ store.cap.value := by
  unfold run
  dsimp only
  split_ifs with hz he hRead hd
  · exact ⟨le_rfl,hp⟩
  · exact ⟨le_rfl,hp⟩
  · have hn := advance_value store pc hRead
    dsimp only
    have ih := run_position_bounds store (a.coinStep b).2 b
      (BinaryIndexWord.incrementWithWork pc).1.1 (advance_bound store pc hRead)
    omega
  · dsimp only
    have hn := advance_value store pc hRead
    have hb := advance_bound store pc hRead
    omega
  · exact ⟨le_rfl,hp⟩
termination_by store.cap.value - pc.value
decreasing_by
  have hr := (guard_value store pc).mp hRead
  have _hn := advance_value store pc hRead
  omega

/-- Reindex the reference cap without changing its list reader. -/
theorem reference_reindex {width : ℕ} (seed : List Bool) (N M : ℕ) (hNM : N = M)
    (a b : FixedBinaryWord width) (pos : ℕ) (hp : pos ≤ N) (hq : pos ≤ M) :
    BinaryStoredCoinIndexed.run N (fun index => seed.getD index.val false) a b pos hp =
      BinaryStoredCoinIndexed.run M (fun index => seed.getD index.val false) a b pos hq := by
  subst M
  rfl

theorem run_prepared_state {width : ℕ} (seed : List Bool) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord (prepare seed).width) (hp : pc.value ≤ (prepare seed).cap.value) :
    decoded (prepare seed) (run (prepare seed) a b pc hp) =
      BinaryStoredCoinIndexed.run seed.length (fun index => seed.getD index.val false)
        a b pc.value (by simpa only [cap_value] using hp) := by
  have h := run_state (prepare seed) a b pc hp
  have hr : reader (prepare seed) = (fun index => seed.getD index.val false) := by
    funext index
    exact reader_prepare seed index
  rw [hr] at h
  exact h.trans (reference_reindex seed _ _ (cap_value seed) a b pc.value hp
    (by simpa only [cap_value] using hp))

open BinaryRationalNormalization

/-- Padding the actual stored words then using the same Boolean controller. -/
def sample (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : Result store :=
  let words := BinaryStoredRationalCoin.fromStored word.numerator word.denominator
  let result := run store words.1 words.2 pc hp
  (result.1,12 * (max word.numerator.length word.denominator.length + 1) + result.2)

theorem sample_state (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    decoded store (sample store word pc hp) =
      BinaryStoredCoinIndexed.sample word store.cap.value (reader store) pc.value hp := by
  unfold sample BinaryStoredCoinIndexed.sample
  simpa only [decoded] using run_state store
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).1
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).2 pc hp

def sampleBound (wordWidth indexWidth remaining : ℕ) : ℕ :=
  12 * (wordWidth + 1) + allowance wordWidth indexWidth * (remaining + 1)

theorem sample_bound (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (W : ℕ) (hW : width word ≤ W) :
    (sample store word pc hp).2 ≤ sampleBound W store.width (store.cap.value - pc.value) := by
  have h := run_bound store
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).1
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).2 pc hp
  unfold sample sampleBound BinaryStoredRationalCoin.fromStored
  dsimp only at *
  unfold width at hW
  apply Nat.add_le_add
  · omega
  · apply h.trans
    apply Nat.mul_le_mul_right
    unfold allowance
    omega

theorem sample_position_bounds (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sample store word pc hp).1.2.value ∧
      (sample store word pc hp).1.2.value ≤ store.cap.value := by
  exact run_position_bounds store
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).1
    (BinaryStoredRationalCoin.fromStored word.numerator word.denominator).2 pc hp

theorem sample_prepared_state (seed : List Bool) (word : SignedWord)
    (pc : FixedBinaryWord (prepare seed).width) (hp : pc.value ≤ (prepare seed).cap.value) :
    decoded (prepare seed) (sample (prepare seed) word pc hp) =
      BinaryStoredCoinIndexed.sample word seed.length (fun index => seed.getD index.val false)
        pc.value (by simpa only [cap_value] using hp) := by
  have h := sample_state (prepare seed) word pc hp
  have hr : reader (prepare seed) = (fun index => seed.getD index.val false) := by
    funext index
    exact reader_prepare seed index
  rw [hr] at h
  apply h.trans
  unfold BinaryStoredCoinIndexed.sample
  exact reference_reindex seed _ _ (cap_value seed) _ _ pc.value hp
    (by simpa only [cap_value] using hp)


end Blotto.BinaryWordIndexCoinController
