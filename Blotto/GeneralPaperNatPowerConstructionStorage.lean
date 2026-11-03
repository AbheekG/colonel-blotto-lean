import Blotto.GeneralPaperPrecallResidentStorage

/-! Repeated-squaring constructor records, raw square, argument controls and
selected halving frames. Powers occur only in this erased storage observer.
Both native child/current annotations are counted, including exponent zero. -/
namespace Blotto.GeneralPaperNatPowerConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperNatPower
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def payload (base E : ℕ) : ℕ :=
  128*(1+binaryWordWidth base+binaryWordWidth E+binaryWordWidth (base^E))

def record (W : ℕ) (r : Result) : ℕ := fields W [r.power,r.steps,r.work]

theorem record_words (base E e : ℕ) (hb : 0<base) (he : e≤E) :
    ∀ x∈[(run base e).power,(run base e).steps,(run base e).work],natBits x≤payload base E := by
  have hp := binaryWordWidth_mono (Nat.pow_le_pow_right hb he)
  have hd := steps_le base e (binaryWordWidth e) (lt_pow_binaryWordWidth e)
  have hew := binaryWordWidth_mono he
  have hs := GeneralPaperInitializerControlCounters.word_le_self (run base e).steps
  have hw := GeneralPaperInitializerControlCounters.word_le_self (run base e).work
  have hdata := data base e
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits payload
  · rw [hdata.1]; omega
  · omega
  · omega

theorem record_bound (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    record W (run base e)≤3*(payload base E+W)+32*W :=
  fields_bound W (payload base E) _ (record_words base E e hb he)

def frame (W base e : ℕ) : ℕ :=
  let child := run base (e/2)
  fields W [base,e,e/2,e%2,child.power*child.power]+
    record W child+record W (run base e)+256*W

theorem frame_bound (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    frame W base e≤12*payload base E+384*W := by
  have hh := GeneralPaperNatPowerOperands.half_power base e hb
  have hp : (run base (e/2)).power*(run base (e/2)).power≤base^E :=
    hh.2.trans (Nat.pow_le_pow_right hb he)
  have hpow := binaryWordWidth_mono hp
  have hew := binaryWordWidth_mono he
  have hhalf := binaryWordWidth_mono (show e/2≤E by omega)
  have hmod := binaryWordWidth_mono ((Nat.mod_le e 2).trans he)
  have hf := fields_bound W (payload base E)
    [base,e,e/2,e%2,(run base (e/2)).power*(run base (e/2)).power] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> unfold natBits payload <;> omega)
  change _≤5*(payload base E+W)+32*W at hf
  have hc := record_bound W base E (e/2) hb (by omega)
  have hr := record_bound W base E e hb he
  unfold frame
  dsimp only
  omega

def peak (W base e : ℕ) : ℕ :=
  frame W base e+if e=0 then 0 else peak W base (e/2)
termination_by e
decreasing_by omega

theorem bounded (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    peak W base e≤((run base e).steps+1)*(12*payload base E+384*W) := by
  have hf := frame_bound W base E e hb he
  rw [peak]
  split
  · rename_i hz
    subst e
    rw [run,ite_eq_left (by rfl)]
    dsimp only
    omega
  · rename_i hn
    have hi := bounded W base E (e/2) hb (by omega)
    have hs : (run base e).steps=(run base (e/2)).steps+1 := by
      rw [run,ite_eq_right hn]
    rw [hs]
    exact (Nat.add_le_add hf hi).trans_eq (by ring)
termination_by e
decreasing_by omega

theorem depth_bound (W base E e : ℕ) (hb : 0<base) (he : e≤E) :
    peak W base e≤(binaryWordWidth E+1)*(12*payload base E+384*W) := by
  have hs := steps_le base e (binaryWordWidth E)
    ((lt_pow_binaryWordWidth e).trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (binaryWordWidth_mono he)))
  exact (bounded W base E e hb he).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hs 1))

end Blotto.GeneralPaperNatPowerConstructionStorage
