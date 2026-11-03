import Blotto.BinaryStoredCountdown
import Blotto.BinaryDecodedInputLength

/-! The native row reader follows a stored Boolean countdown, not an assembled
untrusted dimension. The interpreted count occurs only in dependent proof
indices. Actual remaining frame length bounds all countdown/framing/normalizer
work, including enormous rejected declared counts. Numeric returned-row size,
array/record/controller/physical bookkeeping are separate. -/

namespace Blotto.BinaryStoredDimensionRow
open BinaryRationalNormalization BinaryPRGFrame BinaryStoredCountdown

def read (counter bits : List Bool) : Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × ℕ :=
  let tested := nonzeroWithWork counter
  if hPositive : tested.1 = true then
    let first := BinaryCanonicalFrameWork.read bits
    match hf : first.1 with
    | none => (none,tested.2 + first.2.recorded)
    | some parsed =>
        let smaller := predecessorWithWork counter
        let later := read smaller.1 parsed.2
        let result := later.1.map (fun rest =>
          (⟨parsed.1.val :: rest.1.row,(by
              simp only [List.length_cons,rest.1.length]
              exact predecessor_value counter ((nonzeroWithWork_value counter).mp hPositive)),
            (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                · subst word; exact parsed.1.property
                · exact rest.1.canonical word ht)⟩,rest.2))
        (result,tested.2 + first.2.recorded + smaller.2 + later.2)
  else
    (some (⟨[],(by
        have hFalse : tested.1 = false := Bool.eq_false_iff.mpr hPositive
        exact (nonzeroWithWork_false counter hFalse).symm),by simp⟩,bits),tested.2)
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameWork.read_suffix_lt bits parsed hf

def erase {n : ℕ} (parsed : Words n × List Bool) : List SignedWord × List Bool := (parsed.1.row,parsed.2)

theorem read_raw_state (counter bits : List Bool) :
    (read counter bits).1.map erase =
      (BinaryCanonicalRowReadWork.read (BinaryBigEndian.littleValue counter) bits).1.map erase := by
  unfold read
  dsimp only
  split
  · rename_i hPositive
    have hCount := predecessor_value counter ((nonzeroWithWork_value counter).mp hPositive)
    conv_rhs => rw [← hCount]
    unfold BinaryCanonicalRowReadWork.read
    dsimp only
    split
    · rename_i hf
      simp only [hf,Option.map_none]
    · rename_i first hf
      have ih := read_raw_state (predecessor counter) first.2
      simp only [hf,predecessorWithWork_state,Option.map_map,Function.comp_def,erase]
      simpa only [Option.map_map,Function.comp_def,erase] using congrArg (Option.map (fun rest => (first.1.val :: rest.1,rest.2))) ih
  · rename_i hZero
    have hFalse : (nonzeroWithWork counter).1 = false := Bool.eq_false_iff.mpr hZero
    have hCount := nonzeroWithWork_false counter hFalse
    conv_rhs => rw [hCount]
    rfl
termination_by bits.length
decreasing_by all_goals exact BinaryCanonicalFrameWork.read_suffix_lt _ _ (by assumption)

theorem erase_injective {n : ℕ} : Function.Injective (erase (n := n)) := by
  rintro ⟨⟨row,hl,hc⟩,suffix⟩ ⟨⟨other,ho,hd⟩,tail⟩ h
  have hr := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  dsimp only [erase] at hr ht
  subst other
  subst tail
  rfl

theorem read_state (counter bits : List Bool) :
    (read counter bits).1 = (BinaryCanonicalRowReadWork.read (BinaryBigEndian.littleValue counter) bits).1 := by
  have hr := read_raw_state counter bits
  cases hn : (read counter bits).1 with
  | none =>
      rw [hn,Option.map_none] at hr
      cases ho : (BinaryCanonicalRowReadWork.read (BinaryBigEndian.littleValue counter) bits).1 with
      | none => rfl
      | some parsed => rw [ho,Option.map_some] at hr; cases hr
  | some parsed =>
      rw [hn,Option.map_some] at hr
      cases ho : (BinaryCanonicalRowReadWork.read (BinaryBigEndian.littleValue counter) bits).1 with
      | none => rw [ho,Option.map_none] at hr; cases hr
      | some old =>
          rw [ho,Option.map_some] at hr
          exact congrArg some (erase_injective (Option.some.inj hr))

theorem read_count_bound (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (read counter bits).1 = some parsed) : BinaryBigEndian.littleValue counter ≤ bits.length :=
  BinaryDecodedInputLength.read_row_count _ _ _ ((read_state counter bits).symm.trans h)

theorem read_consumed (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (read counter bits).1 = some parsed) : (parsed.1.row.map width).sum + parsed.2.length ≤ bits.length :=
  BinaryDecodedInputLength.read_row_consumed _ _ _ ((read_state counter bits).symm.trans h)

theorem read_suffix_length (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (read counter bits).1 = some parsed) : parsed.2.length ≤ bits.length := by
  have hc := read_consumed counter bits parsed h
  omega

def bound (counterWidth length : ℕ) : ℕ :=
  (length + 1) * (BinaryCanonicalFrameWork.bound length + 5 * (counterWidth + 1))

theorem read_bound (counter bits : List Bool) : (read counter bits).2 ≤ bound counter.length bits.length := by
  have hFirst := BinaryCanonicalFrameWork.read_bound bits
  unfold read
  dsimp only
  split
  · split
    · change counter.length + 1 + (BinaryCanonicalFrameWork.read bits).2.recorded ≤ _
      unfold bound
      nlinarith
    · rename_i first hf
      have hLen := BinaryCanonicalFrameWork.read_suffix_lt bits first hf
      have hEarlier := BinaryCanonicalFrameWork.bound_mono hLen.le
      have hDec := predecessorWithWork_bound counter
      have ih := read_bound (predecessor counter) first.2
      rw [predecessor_length] at ih
      have ht := ih.trans (Nat.mul_le_mul (show first.2.length + 1 ≤ bits.length by omega)
        (Nat.add_le_add_right hEarlier (5 * (counter.length + 1))))
      change counter.length + 1 + (BinaryCanonicalFrameWork.read bits).2.recorded + (predecessorWithWork counter).2 +
        (read (predecessor counter) first.2).2 ≤ _
      unfold bound
      rw [Nat.add_mul,one_mul]
      omega
  · change counter.length + 1 ≤ _
    unfold bound
    nlinarith
termination_by bits.length
decreasing_by all_goals exact BinaryCanonicalFrameWork.read_suffix_lt _ _ (by assumption)

theorem bound_mono {a b c d : ℕ} (hCounter : a ≤ b) (hLength : c ≤ d) : bound a c ≤ bound b d := by
  have hf := BinaryCanonicalFrameWork.bound_mono hLength
  unfold bound
  gcongr

end Blotto.BinaryStoredDimensionRow
