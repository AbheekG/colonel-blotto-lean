import Blotto.GeneralPaperBasisBudgetStorage

/-! Literal bordered-adjugate scalar entries. Actual decoded indices,
copy/negation/product/sum/exact-quotient operands, primitive scratch and
native branch/partial fields are counted. Validity supplies divisibility;
no quotient result, size certificate or native matrix oracle is supplied. -/
namespace Blotto.GeneralPaperBasisEntryStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def operands {n : ℕ} (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : List ℤ :=
  match GeneralPaperBasisAppendIndex.decode n j,GeneralPaperBasisAppendIndex.decode n k with
  | none,none => [D]
  | some i,none => [au.read i,-(au.read i)]
  | none,some l => [va.read l,-(va.read l)]
  | some i,some l =>
    let p := Dnext*(A.read i).read l
    let q := au.read i*va.read l
    [D,Dnext,(A.read i).read l,au.read i,va.read l,p,q,p+q,(p+q)/D]

theorem operands_bound {n : ℕ} (H U V L : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k) (j k : Fin (n+1)) :
    ∀ z∈operands D Dnext A au va j k,z.natAbs≤GeneralPaperBasisEntryBits.cap H U V L := by
  let M := GeneralPaperBasisEntryBits.cap H U V L
  have hc := GeneralPaperBasisEntryBits.cap_bounds H U V L
  have hd := hD.trans hc.1
  have hn := hNext.trans hc.2.2.2.1
  have ha (i k) := (hA i k).trans hc.1
  have hu (i) := (hU i).trans hc.2.1
  have hv (i) := (hV i).trans hc.2.2.1
  intro z hz
  cases hj : GeneralPaperBasisAppendIndex.decode n j with
  | none =>
    cases hk : GeneralPaperBasisAppendIndex.decode n k with
    | none => simp only [operands,hj,hk,List.mem_singleton] at hz; subst z; exact hd
    | some l =>
      simp only [operands,hj,hk,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · exact hv l
      · simpa only [Int.natAbs_neg] using hv l
  | some i =>
    cases hk : GeneralPaperBasisAppendIndex.decode n k with
    | none =>
      simp only [operands,hj,hk,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · exact hu i
      · simpa only [Int.natAbs_neg] using hu i
    | some l =>
      have hp : (Dnext*(A.read i).read l).natAbs≤L*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hNext (hA i l)
      have hq : (au.read i*va.read l).natAbs≤U*V := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hU i) (hV l)
      have hp' := hp.trans ((Nat.le_add_right (L*H) (U*V)).trans hc.2.2.2.2)
      have hq' := hq.trans ((Nat.le_add_left (U*V) (L*H)).trans hc.2.2.2.2)
      have hs := ((Int.natAbs_add_le _ _).trans (Nat.add_le_add hp hq)).trans hc.2.2.2.2
      have hDiv := GeneralPaperBasisUpdateOperandSize.exact_quotient _ D (hExact i l) M hs
      have hai := ha i l
      have hui := hu i
      have hvi := hv l
      simp only [operands,hj,hk,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega

theorem result_mem {n : ℕ} (model : RationalCostModel) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) :
    (GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).1∈operands D Dnext A au va j k := by
  unfold GeneralPaperBasisEntryBits.run operands
  cases GeneralPaperBasisAppendIndex.decode n j <;> cases GeneralPaperBasisAppendIndex.decode n k <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] <;> tauto

theorem result_word {n : ℕ} (model : RationalCostModel) (W H U V L R : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k)
    (hR : 1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)≤R) (j k : Fin (n+1)) :
    integerBits (GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).1≤R :=
  (Nat.add_le_add_left (binaryWordWidth_mono (operands_bound H U V L D Dnext A au va hD hNext hA hU hV hExact j k _
    (result_mem model W D Dnext A au va j k))) 1).trans hR

def primitiveScratch {n : ℕ} (model : RationalCostModel) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : ℕ :=
  match GeneralPaperBasisAppendIndex.decode n j,GeneralPaperBasisAppendIndex.decode n k with
  | none,none => model.rat (GeneralPaperIntegerPrimitivePrice.word D)
  | some i,none => GeneralPaperIntegerPrimitivePrice.unary model.rat (fun a => -a) (au.read i)
  | none,some l => GeneralPaperIntegerPrimitivePrice.unary model.rat (fun a => -a) (va.read l)
  | some i,some l =>
    let p := Dnext*(A.read i).read l
    let q := au.read i*va.read l
    GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a*b) Dnext ((A.read i).read l)+
      GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a*b) (au.read i) (va.read l)+
      GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) p q+
      GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a/b) (p+q) D

theorem scratch_eq {n : ℕ} (model : RationalCostModel) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) :
    primitiveScratch model D Dnext A au va j k=(GeneralPaperBasisEntryBits.run model.rat 0 D Dnext A au va j k).2 := by
  unfold primitiveScratch GeneralPaperBasisEntryBits.run
  cases GeneralPaperBasisAppendIndex.decode n j <;> cases GeneralPaperBasisAppendIndex.decode n k <;>
    simp only [Nat.mul_zero,Nat.zero_add]

def branchFields {n : ℕ} (model : RationalCostModel) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : List ℕ :=
  match GeneralPaperBasisAppendIndex.decode n j,GeneralPaperBasisAppendIndex.decode n k with
  | none,none =>
    let c := model.rat (GeneralPaperIntegerPrimitivePrice.word D)
    [c,16*W+c]
  | some i,none =>
    let c := GeneralPaperIntegerPrimitivePrice.unary model.rat (fun a => -a) (au.read i)
    [c,16*W+c]
  | none,some l =>
    let c := GeneralPaperIntegerPrimitivePrice.unary model.rat (fun a => -a) (va.read l)
    [c,16*W+c]
  | some i,some l =>
    let p := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a*b) Dnext ((A.read i).read l)
    let q := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a*b) (au.read i) (va.read l)
    let s := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a+b) (Dnext*(A.read i).read l) (au.read i*va.read l)
    let t := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a/b) (Dnext*(A.read i).read l+au.read i*va.read l) D
    [p,q,s,t,32*W+p,32*W+p+q,32*W+p+q+s,32*W+p+q+s+t]

theorem branch_fields {n : ℕ} (model : RationalCostModel) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) :
    ∀ a∈branchFields model W D Dnext A au va j k,a≤(GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).2 := by
  intro a ha
  cases hj : GeneralPaperBasisAppendIndex.decode n j <;> cases hk : GeneralPaperBasisAppendIndex.decode n k
  all_goals simp only [branchFields,hj,hk,List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals simp only [GeneralPaperBasisEntryBits.run,hj,hk]
  all_goals first | (rcases ha with rfl|rfl <;> omega) | (rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)

def decoded {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some i => i.val+1

theorem decoded_bound {n : ℕ} (x : Option (Fin n)) : decoded x≤n+1 := by cases x <;> dsimp only [decoded] <;> omega

def controls {n : ℕ} (model : RationalCostModel) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : List ℕ :=
  branchFields model W D Dnext A au va j k++[n,j.val,k.val,decoded (GeneralPaperBasisAppendIndex.decode n j),
    decoded (GeneralPaperBasisAppendIndex.decode n k),(GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).2,16*W,32*W]

def price (model : RationalCostModel) (W R : ℕ) : ℕ := 32*W+8*model.rat R
def metadataCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+2+3*price model W R+32*W
def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : ℕ :=
  listFootprint W integerBits (operands D Dnext A au va j k)+primitiveScratch model D Dnext A au va j k+
    fields W (controls model W D Dnext A au va j k)+128*W
def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  9*(R+2*W)+32*W+8*model.rat R+16*(natBits (metadataCap model W n R)+W)+160*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W H U V L R : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k)
    (hR : 1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)≤R) (j k : Fin (n+1)) :
    window model W D Dnext A au va j k≤profile model W n R := by
  have hLen : (operands D Dnext A au va j k).length≤9 := by
    unfold operands; cases GeneralPaperBasisAppendIndex.decode n j <;> cases GeneralPaperBasisAppendIndex.decode n k <;>
      simp only [List.length_cons,List.length_nil] <;> omega
  have hOperands := (list_bound W R integerBits (operands D Dnext A au va j k)
    (fun z hz => (Nat.add_le_add_left (binaryWordWidth_mono (operands_bound H U V L D Dnext A au va hD hNext hA hU hV hExact j k z hz)) 1).trans hR)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hScratch : primitiveScratch model D Dnext A au va j k≤8*model.rat R := by
    rw [scratch_eq]
    have h := GeneralPaperBasisEntryBits.work model.rat model.monotone 0 H U V L D Dnext A au va hD hNext hA hU hV hExact j k
    simp only [Nat.mul_zero,Nat.zero_add] at h
    exact h.trans (Nat.mul_le_mul_left 8 (model.monotone hR))
  have hWork := (GeneralPaperBasisEntryBits.work model.rat model.monotone W H U V L D Dnext A au va hD hNext hA hU hV hExact j k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (model.monotone hR)) (32*W))
  change (GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).2≤price model W R at hWork
  have hCount : (controls model W D Dnext A au va j k).length≤16 := by
    unfold controls branchFields
    cases GeneralPaperBasisAppendIndex.decode n j <;> cases GeneralPaperBasisAppendIndex.decode n k <;>
      simp only [List.length_append,List.length_cons,List.length_nil] <;> omega
  have hf := fields_bound W (natBits (metadataCap model W n R)) (controls model W D Dnext A au va j k) (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    rcases List.mem_append.mp ha with ha|ha
    · have h := (branch_fields model W D Dnext A au va j k a ha).trans hWork
      unfold metadataCap; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      have hj := decoded_bound (GeneralPaperBasisAppendIndex.decode n j)
      have hk := decoded_bound (GeneralPaperBasisAppendIndex.decode n k)
      unfold metadataCap
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega)
  have hFields := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) _)
  unfold window profile
  omega

end Blotto.GeneralPaperBasisEntryStorage
