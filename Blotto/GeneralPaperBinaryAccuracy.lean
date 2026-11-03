import Blotto.GeneralPaperStrategyPreparationWork
import Blotto.BinaryRulerPrecisionWork

/-! Exact general-case accuracy from positive Boolean numerator/denominator
words. Cancellation/alignment/lexicographic comparison construct a ruler;
only that short ruler is counted. Large numeric values and the rational
quotient occur only in erased correspondence proofs. -/
namespace Blotto.GeneralPaperBinaryAccuracy
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem ratio_exponent (n d : ℕ) (hn : 0<n) :
    binaryRatioPrecision d n=(GeneralPaperDyadicAccuracy.prepare ((n:ℚ)/d)).exponent := by
  let q : ℚ := (n:ℚ)/d
  let k := binaryRatioPrecision d n
  have hnQ : (0:ℚ)<n := by exact_mod_cast hn
  have hRatio : (d:ℚ)/(n:ℚ)≤(2:ℚ)^k := by
    apply (div_le_iff₀ hnQ).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using binaryRatioPrecision_bound d n hn : d≤2^k*n)
  have hFirst := GeneralPaperDyadicAccuracy.loop_minimal q⁻¹ 1 (by decide) k
    (by simpa only [q,inv_div,Nat.one_mul,Nat.cast_pow,Nat.cast_ofNat] using hRatio)
  have hs := (GeneralPaperDyadicAccuracy.loop_spec q⁻¹ 1 (by decide)).2.1
  rw [(GeneralPaperDyadicAccuracy.loop_spec q⁻¹ 1 (by decide)).1] at hs
  simp only [Nat.one_mul,Nat.cast_pow,Nat.cast_ofNat] at hs
  have hGuard : d≤n*2^(GeneralPaperDyadicAccuracy.prepare q).exponent := by
    have hQ : (d:ℚ)≤(n:ℚ)*(2:ℚ)^(GeneralPaperDyadicAccuracy.prepare q).exponent :=
      by
        have h := (div_le_iff₀ hnQ).mp (by simpa only [q,inv_div] using hs)
        simpa only [q,GeneralPaperDyadicAccuracy.prepare,inv_div,mul_comm] using h
    exact_mod_cast hQ
  have hSecond := binaryRatioPrecision_minimal d n hn _ hGuard
  exact Nat.le_antisymm hSecond hFirst

def count (index : ℕ → ℕ) (A : ℕ) : List Bool → ℕ×ℕ
  | [] => (0,16*A)
  | _::rest =>
    let later := count index A rest
    (later.1+1,later.2+GeneralPaperNaturalPrimitivePrice.binary index (fun a b => a+b) later.1 1+32*A)

theorem count_data (index : ℕ → ℕ) (A : ℕ) (bits : List Bool) : (count index A bits).1=bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [count,ih,List.length_cons]

theorem count_work (index : ℕ → ℕ) (hMono : Monotone index) (A N : ℕ)
    (hCap : index (1+binaryWordWidth (N+1))≤A) (bits : List Bool) (hLength : bits.length≤N) :
    (count index A bits).2≤34*bits.length*A+16*A := by
  induction bits with
  | nil => simp only [count,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons bit rest ih =>
    have hr := ih (by simpa only [List.length_cons] using Nat.le_of_succ_le hLength)
    have hb := GeneralPaperNaturalPrimitivePrice.binary_le index hMono (fun a b => a+b) rest.length 1 (N+1)
      (by simp only [List.length_cons] at hLength;omega) (by omega)
      (by simp only [List.length_cons] at hLength;omega)
    simp only [count,count_data,List.length_cons]
    nlinarith only [hr,hb,hCap]

def prepare (index : ℕ → ℕ) (A : ℕ) (words : BinaryAccuracyWords) : ℕ×ℕ :=
  let ruler := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  let selected := count index A ruler.1
  (selected.1,ruler.2*A+selected.2+64*A)

theorem prepare_data (index : ℕ → ℕ) (A : ℕ) (words : BinaryAccuracyWords) :
    (prepare index A words).1=binaryRatioPrecision words.denominator.value words.numerator.value := by
  dsimp only [prepare]
  rw [count_data,BinaryRulerPrecisionWork.prepare_state,BinaryRulerPrecisionLifetime.prepareWithTrace_state,
    BinaryRulerPrecision.prepare_length,PositiveBinaryWord.ratioPrecision_eq]

theorem exact_exponent (index : ℕ → ℕ) (A : ℕ) (words : BinaryAccuracyWords) (epsilon : ℚ)
    (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value) :
    (prepare index A words).1=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent := by
  rw [prepare_data,hInput]
  exact ratio_exponent _ _ words.numerator.value_pos

theorem prepare_work (index : ℕ → ℕ) (hMono : Monotone index) (A : ℕ) (words : BinaryAccuracyWords)
    (hCap : index (1+binaryWordWidth (words.numerator.width+words.denominator.width+1))≤A) :
    (prepare index A words).2≤128*(words.numerator.width+words.denominator.width+1)*A := by
  have hs := BinaryRulerPrecisionWork.prepare_work words.denominator words.numerator
  have hLength : (BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator).1.length≤words.denominator.width := by
    rw [BinaryRulerPrecisionWork.prepare_state,BinaryRulerPrecisionLifetime.prepareWithTrace_state]
    exact BinaryRulerPrecision.prepare_length_bound _ _
  have hc := count_work index hMono A (words.numerator.width+words.denominator.width) hCap
    (BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator).1 (by omega)
  dsimp only [prepare]
  nlinarith only [hs,hc,hLength]

theorem exponent_bound (index : ℕ → ℕ) (A : ℕ) (words : BinaryAccuracyWords) :
    (prepare index A words).1≤words.denominator.width := by
  dsimp only [prepare]
  rw [count_data,BinaryRulerPrecisionWork.prepare_state,BinaryRulerPrecisionLifetime.prepareWithTrace_state]
  exact BinaryRulerPrecision.prepare_length_bound _ _


structure Parsed where
  words : BinaryAccuracyWords
  exponent : ℕ
  correct : exponent=binaryRatioPrecision words.denominator.value words.numerator.value

def read (index : ℕ → ℕ) (A : ℕ) (frame : List Bool) : Option (Parsed×List Bool)×ℕ :=
  let first := BinaryPositiveWordReadWork.read frame
  match first.1 with
  | none => (none,first.2*A+64*A)
  | some numerator =>
    let second := BinaryPositiveWordReadWork.read numerator.2
    match second.1 with
    | none => (none,(first.2+second.2)*A+64*A)
    | some denominator =>
      let words : BinaryAccuracyWords := ⟨numerator.1,denominator.1⟩
      let selected := prepare index A words
      (some (⟨words,selected.1,prepare_data index A words⟩,denominator.2),
        (first.2+second.2)*A+selected.2+64*A)

def forget (parsed : Parsed×List Bool) : BinaryAccuracyWords×List Bool := (parsed.1.words,parsed.2)

theorem read_data (index : ℕ → ℕ) (A : ℕ) (frame : List Bool) :
    (read index A frame).1.map forget=BinaryAccuracyWords.read frame := by
  unfold read BinaryAccuracyWords.read
  dsimp only
  simp only [←BinaryPositiveWordReadWork.read_state]
  cases (BinaryPositiveWordReadWork.read frame).1 with
  | none => rfl
  | some numerator =>
    dsimp only [Option.bind_some]
    cases (BinaryPositiveWordReadWork.read numerator.2).1 <;> rfl

theorem read_exponent (index : ℕ → ℕ) (A : ℕ) (frame : List Bool) (parsed : Parsed×List Bool)
    (_hRead : (read index A frame).1=some parsed) (epsilon : ℚ)
    (hInput : epsilon=(parsed.1.words.numerator.value:ℚ)/parsed.1.words.denominator.value) :
    parsed.1.exponent=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent := by
  rw [parsed.1.correct,hInput]
  exact ratio_exponent _ _ parsed.1.words.numerator.value_pos

theorem read_work (index : ℕ → ℕ) (hMono : Monotone index) (A : ℕ) (frame : List Bool)
    (hCap : index (1+binaryWordWidth (frame.length+1))≤A) :
    (read index A frame).2≤256*(frame.length+1)*A := by
  have hFirst := BinaryPositiveWordReadWork.read_bound frame
  unfold read
  dsimp only
  split
  · nlinarith only [hFirst]
  · rename_i numerator hn
    have hN := BinaryPositiveWordReadWork.read_consumed frame numerator hn
    have hSecond := BinaryPositiveWordReadWork.read_bound numerator.2
    split
    · nlinarith only [hFirst,hN,hSecond]
    · rename_i denominator hd
      have hD := BinaryPositiveWordReadWork.read_consumed numerator.2 denominator hd
      have hWidths : numerator.1.width+denominator.1.width≤frame.length := by omega
      have hp := prepare_work index hMono A (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)
        ((hMono (Nat.add_le_add_left (binaryWordWidth_mono (Nat.add_le_add_right hWidths 1)) 1)).trans hCap)
      dsimp only at hp ⊢
      nlinarith only [hFirst,hN,hSecond,hD,hp]

theorem read_complete (index : ℕ → ℕ) (A : ℕ) (input : BinaryAccuracyInput) (suffix : List Bool) :
    ∃ parsed,(read index A (BinaryAccuracyFrame.encode input++suffix)).1=some (parsed,suffix) ∧ parsed.words.numeric=input := by
  obtain ⟨words,hWords,hNumeric⟩ := BinaryAccuracyWords.read_encode_append input suffix
  have h := read_data index A (BinaryAccuracyFrame.encode input++suffix)
  rw [hWords] at h
  cases hr:(read index A (BinaryAccuracyFrame.encode input++suffix)).1 with
  | none => rw [hr] at h;cases h
  | some parsed =>
    rw [hr] at h
    have he := Option.some.inj h
    have hw : parsed.1.words=words := congrArg Prod.fst he
    have hs : parsed.2=suffix := congrArg Prod.snd he
    refine ⟨parsed.1,?_,?_⟩
    · rw [←hs]
    · rw [hw]
      exact hNumeric


def input (epsilon : ℚ) (hE : 0<epsilon) : BinaryAccuracyInput :=
  ⟨epsilon.num.toNat,epsilon.den,Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hE),epsilon.den_pos⟩

theorem input_value (epsilon : ℚ) (hE : 0<epsilon) :
    ((input epsilon hE).numerator:ℚ)/(input epsilon hE).denominator=epsilon := by
  dsimp only [input]
  rw [ProbabilityWords.nonnegative_numerator_cast epsilon hE.le]
  exact epsilon.num_div_den

theorem input_length (epsilon : ℚ) (hE : 0<epsilon) :
    (BinaryAccuracyFrame.encode (input epsilon hE)).length=2*rationalWordWidth epsilon := by
  have hn : 0<epsilon.num := Rat.num_pos.mpr hE
  have hNat : epsilon.num.toNat=epsilon.num.natAbs := by omega
  rw [BinaryAccuracyFrame.encode_length]
  dsimp only [input]
  rw [hNat]
  unfold rationalWordWidth
  omega

end Blotto.GeneralPaperBinaryAccuracy
