import Blotto.GeneralPaperFastRationalPairDriver

/-! Actual original-input quotient scalar activation and additive input
rates. All thirteen primitive prices and every scalar partial sum are
counted. The complete borrowed classifier cache belongs to its enclosing
front owner. No whole traversal work is used as primitive scratch. -/
namespace Blotto.GeneralPaperFastInputQuotientStorageRates
open GeneralPaperFastInputQuotient GeneralPaperEncodedScalarStorage
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def charges (model : RationalCostModel) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : List ℕ :=
  let x := b*(c.proxy.Qg:ℚ)
  let q := x.num.natAbs/x.den
  let depth := c.proxy.gridBits+1
  [model.rat (rationalWordWidth x),
    model.rat (max (1+binaryWordWidth x.num.natAbs) (1+binaryWordWidth x.den)),model.rat (1+binaryWordWidth q),
    model.rat (rationalWordWidth (q:ℚ)),model.rat (max (rationalWordWidth x) (rationalWordWidth (q:ℚ))),
    model.rat (rationalWordWidth (x-(q:ℚ))),
    model.rat (max (1+binaryWordWidth 12) (1+binaryWordWidth depth)),model.rat (1+binaryWordWidth (12*depth)),
    model.rat (max (1+binaryWordWidth (12*depth)) (1+binaryWordWidth 2)),model.rat (1+binaryWordWidth (12*depth+2)),
    model.rat (rationalWordWidth (c.proxy.Qg:ℚ)),
    model.rat (max (rationalWordWidth b) (rationalWordWidth (c.proxy.Qg:ℚ))),model.rat (rationalWordWidth x)]

def partials (xs : List ℕ) : List ℕ := (List.range (xs.length+1)).map (fun i => (xs.take i).sum)

theorem partial_bound (xs : List ℕ) : ∀ z∈partials xs,z≤xs.sum := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  have h := List.sum_take_add_sum_drop xs i
  omega

theorem work_sum (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    (run model W c b).2=(charges model c b).sum+128*W := by
  dsimp only [run,floor,charges,GeneralPaperNaturalPrimitivePrice.binary,GeneralPaperNaturalPrimitivePrice.word,
    GeneralPaperRationalPrimitivePrice.binary,RationalExpression.pairWidth,List.sum_cons,List.sum_nil]
  omega

def controls (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : List ℕ :=
  let x := b*(c.proxy.Qg:ℚ)
  let depth := c.proxy.gridBits+1
  let cast := model.rat (rationalWordWidth (c.proxy.Qg:ℚ))
  let mul := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b c.proxy.Qg
  let found := floor model W depth x
  [W,c.proxy.Qg,depth,x.num.natAbs,x.den,x.num.natAbs/x.den,12,12*depth,2,12*depth+2,64*W,128*W,
    found.2,(run model W c b).2,found.2+cast,found.2+cast+mul,32*W]++charges model c b++partials (charges model c b)

theorem controls_length (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    (controls model W c b).length=44 := by
  simp only [controls,charges,partials,List.length_append,List.length_map,List.length_range,List.length_cons,List.length_nil]

def metadataCap (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : ℕ :=
  let x := b*(c.proxy.Qg:ℚ)
  x.num.natAbs+x.den+c.proxy.Qg+12*(c.proxy.gridBits+1)+profile model W m k B+W+32

theorem control_values (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hB : RationalHeight b B) :
    ∀ z∈controls model W c b,z≤metadataCap model W m k B c b := by
  have hWork := work model W m k c hc b B hB
  have hSum := work_sum model W c b
  have hQ := Nat.div_le_self (b*(c.proxy.Qg:ℚ)).num.natAbs (b*(c.proxy.Qg:ℚ)).den
  have hFound : (floor model W (c.proxy.gridBits+1) (b*(c.proxy.Qg:ℚ))).2+
      model.rat (rationalWordWidth (c.proxy.Qg:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) b c.proxy.Qg+64*W=(run model W c b).2 := rfl
  intro z hz
  simp only [controls,List.mem_append] at hz
  rcases hz with (hz|hz)|hz
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals dsimp only [metadataCap,profile] at *;omega
  · have hzSum : z≤(charges model c b).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) z hz
    dsimp only [metadataCap]
    omega
  · have hzSum := partial_bound (charges model c b) z hz
    dsimp only [metadataCap]
    omega

theorem word_caps (m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (hc : c=GeneralPaperPrecallCachePrice.specification m k)
    (b : ℚ) (hB : RationalHeight b B) :
    rationalWordWidth b≤width m k B ∧ rationalWordWidth (c.proxy.Qg:ℚ)≤width m k B ∧
      rationalWordWidth (b*(c.proxy.Qg:ℚ))≤width m k B ∧
      floorWidth (b*(c.proxy.Qg:ℚ)) (c.proxy.gridBits+1)≤width m k B := by
  have hb := rationalWordWidth_of_height hB
  have hq := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.proxy.Qg)
  have hx := rationalWordWidth_of_height (hB.mul (GeneralPaperBasisDivideBits.nat_height c.proxy.Qg))
  rw [hc] at hq hx ⊢
  dsimp only [GeneralPaperPrecallCachePrice.specification] at hq hx ⊢
  unfold width floorWidth
  omega

theorem metadata_word (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hB : RationalHeight b B) :
    natBits (metadataCap model W m k B c b)≤4*width m k B+natBits (profile model W m k B)+W+16 := by
  let x := b*(c.proxy.Qg:ℚ)
  let depth := c.proxy.gridBits+1
  have hWords := word_caps m k B c hc b hB
  have hn : binaryWordWidth x.num.natAbs≤width m k B := by unfold rationalWordWidth at hWords;dsimp only [x];omega
  have hd : binaryWordWidth x.den≤width m k B := by unfold rationalWordWidth at hWords;dsimp only [x];omega
  have hQ : binaryWordWidth c.proxy.Qg≤width m k B := by
    rw [hc]
    dsimp only [GeneralPaperPrecallCachePrice.specification]
    unfold width
    omega
  have hDepth := GeneralPaperInitializerControlCounters.word_le_self (12*depth)
  have hD : binaryWordWidth (12*depth)≤width m k B := by
    unfold depth width at *
    rw [hc] at hDepth
    rw [hc]
    dsimp only [GeneralPaperPrecallCachePrice.specification] at hDepth
    dsimp only [GeneralPaperPrecallCachePrice.specification]
    omega
  have hw := GeneralPaperInitializerControlCounters.word_le_self W
  have ha := GeneralPaperReferenceScaling.word_add x.num.natAbs x.den
  have hb := GeneralPaperReferenceScaling.word_add (x.num.natAbs+x.den) c.proxy.Qg
  have hcc := GeneralPaperReferenceScaling.word_add (x.num.natAbs+x.den+c.proxy.Qg) (12*depth)
  have hdd := GeneralPaperReferenceScaling.word_add (x.num.natAbs+x.den+c.proxy.Qg+12*depth) (profile model W m k B)
  have he := GeneralPaperReferenceScaling.word_add (x.num.natAbs+x.den+c.proxy.Qg+12*depth+profile model W m k B) W
  have hf := GeneralPaperReferenceScaling.word_add (x.num.natAbs+x.den+c.proxy.Qg+12*depth+profile model W m k B+W) 32
  have h32 : binaryWordWidth 32=6 := by decide
  unfold metadataCap natBits
  change 1+binaryWordWidth (x.num.natAbs+x.den+c.proxy.Qg+12*depth+profile model W m k B+W+32)≤_
  omega

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : ℕ :=
  let x := b*(c.proxy.Qg:ℚ)
  let q := x.num.natAbs/x.den
  rationalWordWidth b+rationalWordWidth (c.proxy.Qg:ℚ)+rationalWordWidth x+rationalWordWidth (q:ℚ)+rationalWordWidth (x-(q:ℚ))+
    (charges model c b).sum+fields W (controls model W c b)+192*W

def storageProfile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  5*width m k B+13*model.rat (width m k B)+44*(4*width m k B+natBits (profile model W m k B)+2*W+16)+224*W

theorem bounded (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hB : RationalHeight b B) :
    window model W c b≤storageProfile model W m k B := by
  have hWords := word_caps m k B c hc b hB
  have hFloor := floor_words (b*(c.proxy.Qg:ℚ)) (c.proxy.gridBits+1)
  have hWork := work model W m k c hc b B hB
  have hSum := work_sum model W c b
  have hCap := metadata_word model W m k B c hc b hB
  have hf := fields_bound W (4*width m k B+natBits (profile model W m k B)+W+16) (controls model W c b) (by
    intro z hz
    exact (Nat.add_le_add_left (binaryWordWidth_mono (control_values model W m k B c hc b hB z hz)) 1).trans hCap)
  rw [controls_length] at hf
  dsimp only [window,storageProfile,profile] at *
  omega

def rate (x : Input) : ℕ := x.B+1+monomial 1 0 1 x

theorem input_rate : Soft rate Input.B := rate_mono (identity Input.B) (fun x => by unfold rate;omega)

theorem lift_source {f : Input → ℕ} (hf : Rated f 1 0 1) : Soft rate f := rate_mono hf (fun x => by unfold rate;omega)

def zeroWidthCertificate : Certificate (fun x => width x.m x.k 0) := by
  have hm := GeneralPaperSourceEndpointFractionConstructionStorageRates.classifier_measure_sharp
  have hQ := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hGrid : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).gridBits) 1 0 1 := by
    apply GeneralPaperSourceSoftBounds.dominated hm
    intro x
    have h := (GeneralPaperPrecallControlWord.root_controls x.m x.k).1
    change (GeneralPaperProxyParameters.prepare x.m x.k).gridBits+4≤GeneralPaperPrecallControlWord.measure x.m x.k at h
    omega
  refine ⟨_,_,_,by unfold width;source_space⟩

theorem width_degrees : (zeroWidthCertificate.fields,zeroWidthCertificate.symbols,zeroWidthCertificate.accuracy)=(1,0,1) := rfl

theorem width_affine (m k B : ℕ) : width m k B=32*B+width m k 0 := by unfold width;omega

theorem width_rate : Soft rate (fun x => width x.m x.k x.B) := by
  have h := add_same (poly_mul_rate (poly_constant 32) input_rate) (lift_source zeroWidthCertificate.bound)
  exact GeneralPaperSourceSoftBounds.dominated h (fun x => by rw [width_affine])

@[fun_prop]
theorem width_small : Small (fun x => width x.m x.k x.B) := by unfold width;fun_prop

theorem quotient_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => profile model (W x) x.m x.k x.B) := by
  have hPrimitive := primitive_preserves hg width_rate width_small
  have hWord : Soft rate W := rate_mono (poly_tight W hW) (fun x => by unfold rate;omega)
  exact add_same (poly_mul_rate (poly_constant 13) hPrimitive) (poly_mul_rate (poly_constant 128) hWord)

theorem profile_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hw := of_tight hW
  dsimp only [profile,GeneralPaperFastRationalMajorant.model]
  fun_prop

theorem storage_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft rate (fun x => storageProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hPrimitive := charge_preserves (C+1) d width_rate width_small
  have hProfile := profile_small C d W hW
  have hNat : Polylog (fun x => natBits (profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)) := by unfold natBits;fun_prop
  have hNatRate : Soft rate (fun x => natBits (profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)) :=
    rate_mono hNat (fun x => by unfold rate;omega)
  have hWord : Soft rate W := rate_mono (poly_tight W hW) (fun x => by unfold rate;omega)
  have hConstant : Soft rate (fun _ => 16) := rate_mono (poly_constant 16) (fun x => by unfold rate;omega)
  have hFields := add_same (add_same (add_same (poly_mul_rate (poly_constant 4) width_rate) hNatRate)
    (poly_mul_rate (poly_constant 2) hWord)) hConstant
  exact add_same (add_same (add_same (poly_mul_rate (poly_constant 5) width_rate)
    (poly_mul_rate (poly_constant 13) hPrimitive)) (poly_mul_rate (poly_constant 44) hFields))
    (poly_mul_rate (poly_constant 224) hWord)

def selectionWidth (x : Input) (B : ℕ) : ℕ :=
  GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare x.m x.k).Qg B

def selectionCertificate : Certificate (fun x => selectionWidth x 0) := by
  have hQ := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  refine ⟨_,_,_,by unfold selectionWidth GeneralPaperSelectionPoints.width;source_space⟩

theorem selection_degrees : (selectionCertificate.fields,selectionCertificate.symbols,selectionCertificate.accuracy)=(1,0,1) := rfl

theorem selection_rate : Soft rate (fun x => selectionWidth x x.B) := by
  have h := add_same (poly_mul_rate (poly_constant 4) input_rate) (lift_source selectionCertificate.bound)
  apply GeneralPaperSourceSoftBounds.dominated h
  intro x
  unfold selectionWidth GeneralPaperSelectionPoints.width
  omega

@[fun_prop]
theorem selection_small : Small (fun x => selectionWidth x x.B) := by
  unfold selectionWidth GeneralPaperSelectionPoints.width
  fun_prop

def inputOverhead (model : RationalCostModel) (m k B : ℕ) : ℕ :=
  13*model.rat (width m k B)+512*model.rat (GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare m k).Qg B)

theorem overhead_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Soft rate (fun x => inputOverhead model x.m x.k x.B) :=
  add_same (poly_mul_rate (poly_constant 13) (primitive_preserves hg width_rate width_small))
    (poly_mul_rate (poly_constant 512) (primitive_preserves hg selection_rate selection_small))

theorem source_split (model : RationalCostModel) (W m k Qv B : ℕ) :
    GeneralPaperFastInputClassifier.sourceProfile model W m k Qv B≤
      GeneralPaperFastInputClassifier.sourceProfile model W m k Qv 0+inputOverhead model m k B := by
  dsimp only [GeneralPaperFastInputClassifier.sourceProfile,GeneralPaperFastInputClassifier.prepareProfile,
    GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.queryProfile,profile,inputOverhead]
  omega

theorem actual_source_input_cost (model : RationalCostModel) (W m k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    (GeneralPaperFastInputClassifier.source model W m k Qv b).2≤
      GeneralPaperFastInputClassifier.sourceProfile model W m k Qv 0+inputOverhead model m k B :=
  (GeneralPaperFastInputClassifier.source_work model W m k Qv b hb B hB).trans (source_split model W m k Qv B)

theorem actual_driver_input_cost {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) (Wf : ℕ) :
    let W := GeneralPaperCachedBitPairReferenceContract.width C d x
    (GeneralPaperFastRationalPairDriver.run model W Wf x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
      GeneralPaperFastInputClassifier.sourceProfile model Wf x.m x.k x.Qv 0+inputOverhead model x.m x.k x.B+
        GeneralPaperFastRationalPairDriver.gridPrice model x.m x.k x.Qv+128+
        GeneralPaperCachedBitPairStorage.price model C d W x.m x.k x.Qv+192*W := by
  have h := GeneralPaperFastRationalPairDriver.work_at_cached_reference hg x hm hQv hp Wf
  have hs := source_split model Wf x.m x.k x.Qv x.B
  dsimp only [GeneralPaperFastRationalPairDriver.price,GeneralPaperFastRationalPairDriver.preparePrice] at h
  omega

end Blotto.GeneralPaperFastInputQuotientStorageRates
