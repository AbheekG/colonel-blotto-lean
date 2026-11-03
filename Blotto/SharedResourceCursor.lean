import Blotto.RationalResourceMachine
import Blotto.CachedWordCursor

/-! A pending resource choice retains one state and two endpoint values.
The two deferred successor states exist only in the refinement view. The
representation itself contains no successor-state pair or expanded tree. -/

namespace Blotto

structure ResourceChoice {n : ℕ} (L : Fin n → ℚ) where
  state : RationalActiveResources L
  first : Fin n
  second : Fin n
  tail : List (Fin n)
  head_pair : state.active = first :: second :: tail
  lower : ℚ
  upper : ℚ
  lower_correct : lower = (state.pair first second tail head_pair).lower
  upper_correct : upper = (state.pair first second tail head_pair).upper

namespace ResourceChoice

def successor {n : ℕ} {L : Fin n → ℚ} (choice : ResourceChoice L) (upperBranch : Bool) : RationalResourceCursor L :=
  .selected choice.state choice.first choice.second choice.tail choice.head_pair
    (if upperBranch then choice.upper else choice.lower)

def select {n : ℕ} {L : Fin n → ℚ} (choice : ResourceChoice L) (upperBranch : Bool) : RationalActiveResources L :=
  choice.state.update choice.first choice.second choice.tail choice.head_pair
    (if upperBranch then choice.upper else choice.lower)

theorem select_eq_materialize {n : ℕ} {L : Fin n → ℚ} (choice : ResourceChoice L) (upperBranch : Bool) :
    choice.select upperBranch = (choice.successor upperBranch).materialize := rfl

theorem select_length_lt {n : ℕ} {L : Fin n → ℚ} (choice : ResourceChoice L) (upperBranch : Bool) :
    (choice.select upperBranch).active.length < choice.state.active.length := by
  apply choice.state.update_length_lt choice.first choice.second choice.tail choice.head_pair
  cases upperBranch
  · exact Or.inl choice.lower_correct
  · exact Or.inr choice.upper_correct

end ResourceChoice

structure PreparedResourceChoice {n : ℕ} (L : Fin n → ℚ) where
  choice : ResourceChoice L
  words : ProbabilityWords

inductive ResourcePreparation {n : ℕ} (L : Fin n → ℚ) where
  | done (state : RationalActiveResources L)
  | ask (prepared : PreparedResourceChoice L)

namespace ResourcePreparation

def decode {n : ℕ} {L : Fin n → ℚ} : ResourcePreparation L → WordTransition (RationalResourceCursor L) (RationalActiveResources L)
  | .done state => .done state
  | .ask prepared => .ask prepared.words.numerator prepared.words.denominator
      prepared.words.denominator_pos prepared.words.normalized
      (prepared.choice.successor true) (prepared.choice.successor false)

end ResourcePreparation

def prepareResourceChoice {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) : ResourcePreparation L := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact .done ⟨resource, [], hn, hm⟩
    | cons a rest =>
      cases rest with
      | nil => exact .done ⟨resource, [a], hn, hm⟩
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := state.pair a b tail rfl
        let registers := RationalPairProgram.run p
        exact .ask ⟨⟨state, a, b, tail, rfl, registers.getD 7 0, registers.getD 8 0,
          RationalPairProgram.run_lower p, RationalPairProgram.run_upper p⟩,
          RationalPairProgram.words p registers rfl⟩

theorem prepareResourceChoice_refines {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) :
    (prepareResourceChoice state).decode = rationalResourceStep state := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail => rfl

inductive SharedResourceCursor {n : ℕ} (L : Fin n → ℚ) where
  | ready (state : RationalActiveResources L)
  | coin {w : ℕ} (choice : ResourceChoice L) (a b : FixedBinaryWord w)
      (positive : 0 < b.value) (normalized : a.value ≤ b.value)

namespace SharedResourceCursor

def decode {n : ℕ} {L : Fin n → ℚ} : SharedResourceCursor L → CachedWordCursor (RationalResourceCursor L)
  | .ready state => .state (.ready state)
  | .coin choice a b hb hab => .coin a b hb hab (choice.successor true) (choice.successor false)

def prepared {n : ℕ} {L : Fin n → ℚ} (p : PreparedResourceChoice L) : SharedResourceCursor L :=
  let w := binaryWordWidth p.words.denominator
  let a := FixedBinaryWord.ofNat w p.words.numerator
  let b := FixedBinaryWord.ofNat w p.words.denominator
  have hA := FixedBinaryWord.value_ofNat w p.words.numerator (p.words.normalized.trans_lt (lt_pow_binaryWordWidth _))
  have hB := FixedBinaryWord.value_ofNat w p.words.denominator (lt_pow_binaryWordWidth _)
  .coin p.choice a b (by rw [hB]; exact p.words.denominator_pos) (by rw [hA, hB]; exact p.words.normalized)

theorem decode_prepared {n : ℕ} {L : Fin n → ℚ} (p : PreparedResourceChoice L) :
    (prepared p).decode = CachedWordCursor.ofWords p.words.numerator p.words.denominator
      p.words.denominator_pos p.words.normalized (p.choice.successor true) (p.choice.successor false) := rfl

def rank {n : ℕ} {L : Fin n → ℚ} (cursor : SharedResourceCursor L) : ℕ :=
  (rationalResourceMachine L).cachedCursorRank cursor.decode

end SharedResourceCursor
end Blotto
