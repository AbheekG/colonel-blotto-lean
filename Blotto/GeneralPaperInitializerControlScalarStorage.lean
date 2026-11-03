import Blotto.GeneralPaperPowerCeilingStorage

/-! Full literal initializer scalar construction: all original products,
rational casts/divisions/subtraction, signed casts/auxiliary numerator,
constant primitive scratch and every native group/parent price prefix.
The fixed price lists observe sixteen scalar calls; no data census runs. -/
namespace Blotto.GeneralPaperInitializerControlScalarStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def naturals (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [4,m,H,p,q,c.first,c.shared,c.third,c.N,c.chosen,c.square,c.scaled]
def rationals (m H p q : ℕ) (reciprocal : Bool) : List ℚ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [(m:ℚ),(p:ℚ),(q:ℚ),(c.N:ℚ),GeneralPaperInitializerControlWork.beta p q reciprocal,
    (m:ℚ)/c.N,GeneralPaperInitializerControlWork.beta p q reciprocal-(m:ℚ)/c.N]
def integers (m H p q : ℕ) (reciprocal : Bool) : List ℤ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [(c.scaled:ℤ),(m:ℤ),(c.scaled:ℤ)-(m:ℤ)]
def naturalPrices (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 4 m,
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.first H,
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.shared p,
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.third q,
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.chosen c.chosen,
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.shared c.square]
def castPrices (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [model.rat (rationalWordWidth (m:ℚ)),model.rat (rationalWordWidth (p:ℚ)),model.rat (rationalWordWidth (q:ℚ)),
    model.rat (rationalWordWidth (c.N:ℚ)),model.rat (GeneralPaperIntegerPrimitivePrice.word (c.scaled:ℤ)),
    model.rat (GeneralPaperIntegerPrimitivePrice.word (m:ℤ))]
def rationalPrices (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (q:ℚ) (p:ℚ)
     else GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (p:ℚ) (q:ℚ),
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (m:ℚ) (c.N:ℚ),
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a-b)
      (GeneralPaperInitializerControlWork.beta p q reciprocal) ((m:ℚ)/c.N)]
def signedPrice (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a-b) (c.scaled:ℤ) (m:ℤ)
def primitivePrices (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  naturalPrices model m H p q reciprocal++castPrices model m H p q reciprocal++rationalPrices model m H p q reciprocal++
    [signedPrice model m H p q reciprocal]
def groupPrices (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  [GeneralPaperInitializerControlBits.naturalWork model m H p q c,GeneralPaperInitializerControlBits.casts model m p q c,
    GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c,signedPrice model m H p q reciprocal]
def prefixes : List ℕ → List ℕ
  | [] => [0]
  | a::as => 0::(prefixes as).map (a+·)
def controls (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  prefixes (naturalPrices model m H p q reciprocal)++prefixes (castPrices model m H p q reciprocal)++
    prefixes (rationalPrices model m H p q reciprocal)++prefixes (groupPrices model m H p q reciprocal)++
    primitivePrices model m H p q reciprocal++[GeneralPaperFinalStaticLoopStorage.bit reciprocal]
def window (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) : ℕ :=
  ((naturals m H p q reciprocal).map natBits).sum+((rationals m H p q reciprocal).map rationalWordWidth).sum+
    ((integers m H p q reciprocal).map integerBits).sum+(primitivePrices model m H p q reciprocal).sum+
    fields W (controls model m H p q reciprocal)+256*W
def metadataCap (model : RationalCostModel) (R : ℕ) : ℕ := 26*model.rat R+1
def profile (model : RationalCostModel) (W R : ℕ) : ℕ := 22*R+26*model.rat R+40*(natBits (metadataCap model R)+W)+288*W

theorem prefixes_length (xs : List ℕ) : (prefixes xs).length=xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [prefixes,List.length_cons,List.length_map,ih]

theorem prefixes_bound (xs : List ℕ) (z : ℕ) (hz : z∈prefixes xs) : z≤xs.sum := by
  induction xs generalizing z with
  | nil =>
    simp only [prefixes,List.mem_cons,List.not_mem_nil,or_false] at hz
    subst z
    exact Nat.zero_le _
  | cons a xs ih =>
    simp only [prefixes,List.mem_cons,List.mem_map] at hz
    rcases hz with rfl|⟨v,hv,rfl⟩
    · exact Nat.zero_le _
    · have h := ih v hv
      simp only [List.sum_cons]
      omega

theorem natural_sum (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    (naturalPrices model m H p q reciprocal).sum=GeneralPaperInitializerControlBits.naturalWork model m H p q
      (GeneralPaperInitializerProducts.run m H p q reciprocal) := by
  simp only [naturalPrices,List.sum_cons,List.sum_nil,GeneralPaperInitializerControlBits.naturalWork]
  omega
theorem cast_sum (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    (castPrices model m H p q reciprocal).sum=GeneralPaperInitializerControlBits.casts model m p q
      (GeneralPaperInitializerProducts.run m H p q reciprocal) := by
  simp only [castPrices,List.sum_cons,List.sum_nil,GeneralPaperInitializerControlBits.casts]
  omega
theorem rational_sum (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    (rationalPrices model m H p q reciprocal).sum=GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal
      (GeneralPaperInitializerProducts.run m H p q reciprocal) := by
  simp only [rationalPrices,List.sum_cons,List.sum_nil,GeneralPaperInitializerControlBits.rationalWork]
  omega
theorem total_sum (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    (primitivePrices model m H p q reciprocal).sum=(groupPrices model m H p q reciprocal).sum := by
  simp only [primitivePrices,List.sum_append,List.sum_cons,List.sum_nil,natural_sum,cast_sum,rational_sum,groupPrices]
  omega

theorem bounded (model : RationalCostModel) (W m H p q R : ℕ) (reciprocal : Bool)
    (hR : GeneralPaperInitializerControlSize.width m H p q≤R) : window model W m H p q reciprocal≤profile model W R := by
  obtain ⟨n4,nm,nH,np,nq,n1,n2,n3,nN,nc,ns,nb⟩ := GeneralPaperInitializerControlSize.natural_words m H p q reciprocal
  obtain ⟨rm,rp,rq,rN,rb,rt,ra⟩ := GeneralPaperInitializerControlSize.rational_words m H p q reciprocal
  obtain ⟨ib,im,ia⟩ := GeneralPaperInitializerControlSize.signed_words m H p q reciprocal
  have hNaturals := sum_bound natBits R (naturals m H p q reciprocal) (by
    intro z hz
    change 1+binaryWordWidth z≤R
    simp only [naturals,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  have hRationals := sum_bound rationalWordWidth R (rationals m H p q reciprocal) (by
    intro z hz
    simp only [rationals,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  have hIntegers := sum_bound integerBits R (integers m H p q reciprocal) (by
    intro z hz
    simp only [integers,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> exact (by first | exact ib.trans hR | exact im.trans hR | exact ia.trans hR))
  have hn := (GeneralPaperInitializerControlBits.natural_work model m H p q reciprocal).trans (Nat.mul_le_mul_left 12 (model.monotone hR))
  have hc := (GeneralPaperInitializerControlBits.casts_work model m H p q reciprocal).trans (Nat.mul_le_mul_left 6 (model.monotone hR))
  have hr := (GeneralPaperInitializerControlBits.rational_work model m H p q reciprocal).trans (Nat.mul_le_mul_left 6 (model.monotone hR))
  have hi := (GeneralPaperIntegerWordPrice.integer_binary model.rat model.monotone (fun a b => a-b) _ _ R
    (ib.trans hR) (im.trans hR) (ia.trans hR))
  have hGroups : (groupPrices model m H p q reciprocal).sum≤26*model.rat R := by
    simp only [groupPrices,List.sum_cons,List.sum_nil]
    change signedPrice model m H p q reciprocal≤2*model.rat R at hi
    omega
  have hTotal : (primitivePrices model m H p q reciprocal).sum≤26*model.rat R := by rw [total_sum]; exact hGroups
  have hNatPrice : (naturalPrices model m H p q reciprocal).sum≤26*model.rat R := by rw [natural_sum]; omega
  have hCastPrice : (castPrices model m H p q reciprocal).sum≤26*model.rat R := by rw [cast_sum]; omega
  have hRatPrice : (rationalPrices model m H p q reciprocal).sum≤26*model.rat R := by rw [rational_sum]; omega
  have hBit := GeneralPaperFinalStaticLoopStorage.bit_bound reciprocal
  have hCount : (controls model m H p q reciprocal).length=40 := by
    simp only [controls,List.length_append,prefixes_length,naturalPrices,castPrices,rationalPrices,groupPrices,primitivePrices,List.length_cons,List.length_nil]
  have hf := fields_bound W (natBits (metadataCap model R)) (controls model m H p q reciprocal) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with ((((hNat|hCast)|hRat)|hGroup)|hPrimitive)|hTag
    · have h := prefixes_bound _ _ hNat; omega
    · have h := prefixes_bound _ _ hCast; omega
    · have h := prefixes_bound _ _ hRat; omega
    · have h := prefixes_bound _ _ hGroup; omega
    · have h := List.single_le_sum (fun n _ => Nat.zero_le n) z hPrimitive; omega
    · subst z; omega)
  rw [hCount] at hf
  change _≤12*R at hNaturals
  change _≤7*R at hRationals
  change _≤3*R at hIntegers
  unfold window profile
  omega

end Blotto.GeneralPaperInitializerControlScalarStorage
