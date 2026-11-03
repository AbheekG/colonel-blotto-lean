import Blotto.BinarySequentialPayloadDecoder

/-! A balanced native-word encoder crops each low child before recursing and
passes the high child's actual returned suffix to the low child. It constructs
one output cell per leaf, with no per-bit wide-word indexing, array buffer or
append copy. Primitive and storage prices are treated separately. -/
namespace Blotto.BinaryBalancedWordEncoder
set_option autoImplicit false

def masked (value width : ℕ) : ℕ := value &&& ((1 <<< width)-1)

theorem masked_bound (value width : ℕ) : masked value width < 2^width := by
  unfold masked
  rw [Nat.shiftLeft_eq,one_mul,Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos width)

theorem shifted_bound (length low value : ℕ) (hLow : low ≤ length) (hValue : value < 2^length) :
    value >>> low < 2^(length-low) := by
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos low)).mpr
  rw [← pow_add,show length-low+low = length by omega]
  exact hValue

def into (length value : ℕ) (suffix : List Bool) : List Bool :=
  if length = 0 then suffix else if length = 1 then value.testBit 0::suffix else
    let low := length/2
    let high := into (length-low) (value >>> low) suffix
    into low (masked value low) high
termination_by length
decreasing_by all_goals omega

theorem bits_split (length low value : ℕ) (hLow : low ≤ length) :
    BinaryPayload.bits length value =
      BinaryPayload.bits low (masked value low)++BinaryPayload.bits (length-low) (value >>> low) := by
  apply List.ext_getElem
  · simp only [BinaryPayload.bits_length,List.length_append]
    omega
  · intro j hj hk
    have hLeft : (BinaryPayload.bits low (masked value low)).length = low := BinaryPayload.bits_length _ _
    by_cases h : j < low
    · rw [List.getElem_append_left (by omega : j < (BinaryPayload.bits low (masked value low)).length)]
      simp only [BinaryPayload.bits,List.getElem_ofFn]
      simp only [masked,Nat.shiftLeft_eq,one_mul,Nat.testBit_and,Nat.testBit_two_pow_sub_one,h,decide_true,Bool.and_true]
    · rw [List.getElem_append_right (by omega : (BinaryPayload.bits low (masked value low)).length ≤ j)]
      simp only [BinaryPayload.bits,List.getElem_ofFn,List.length_ofFn,Nat.testBit_shiftRight]
      congr 1
      omega

theorem into_data (length value : ℕ) (suffix : List Bool) : into length value suffix = BinaryPayload.bits length value++suffix := by
  unfold into
  split
  · rename_i hz
    simp [hz,BinaryPayload.bits]
  · split
    · rename_i hOne
      subst length
      simp [BinaryPayload.bits,List.ofFn_succ]
    · dsimp only
      rw [into_data,into_data,bits_split length (length/2) value (by omega),List.append_assoc]
termination_by length
decreasing_by all_goals omega

theorem into_length (length value : ℕ) (suffix : List Bool) : (into length value suffix).length = length+suffix.length := by
  rw [into_data,List.length_append,BinaryPayload.bits_length]

def bits (value : ℕ) : List Bool := into (binaryWordWidth value) value []

theorem bits_data (value : ℕ) : bits value = BinaryPayload.bits (binaryWordWidth value) value := by
  simp only [bits,into_data,List.append_nil]

theorem bits_length (value : ℕ) : (bits value).length = binaryWordWidth value := by
  rw [bits_data,BinaryPayload.bits_length]

theorem bits_decode (value : ℕ) : BinaryPayload.decode (bits value) = value := by
  rw [bits_data]
  exact BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth value)

end Blotto.BinaryBalancedWordEncoder
