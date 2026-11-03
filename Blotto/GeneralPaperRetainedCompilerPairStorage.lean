import Blotto.GeneralPaperSourceModifiedColumnReachedRates
import Blotto.GeneralPaperRetainedCompilerPairBits

/-! Complete physical compiler-pair caller. Both original players remain
resident while precisely the selected child executes. Returned pair owners,
reached endpoint scratch, values, classifier and native parent fields are
counted. All observers are erased; no census enters the data path. -/
namespace Blotto.GeneralPaperRetainedCompilerPairStorage
open GeneralPaperOriginalDrawEquilibrium GeneralPaperEnclosingSourceOwners GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def pairFoot {T m K : ℕ} (W : ℕ) (columns : Columns T m K) : ℕ :=
  columnsFoot W columns.rich+columnsFoot W columns.poor+64*W

def pairProfile (W T m K R : ℕ) : ℕ := 2*columnsProfile W T m K R+64*W

def optionFoot {T m K : ℕ} (W : ℕ) : Option (Columns T m K) → ℕ
  | none => 1
  | some columns => 1+pairFoot W columns+32*W

def child {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) : Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))×ℕ :=
  match classified.choice.modify with
  | none => (none,0)
  | some .rich => GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.rich values 1 proxyValue false (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint
  | some .poor => GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.poor values proxyValue 1 true (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint

def activeWindow {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) : ℕ :=
  match classified.choice.modify with
  | none => 0
  | some .rich => GeneralPaperRetainedModifiedColumnStorage.window model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.rich values 1 proxyValue false (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint outer ho inner hi
  | some .poor => GeneralPaperRetainedModifiedColumnStorage.window model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.poor values proxyValue 1 true (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint outer ho inner hi

def endpointWork (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) : ℕ :=
  match c.choice.modify with
  | none => 0
  | some _ => (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ c).2

def endpointWindow (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) : ℕ :=
  match c.choice.modify with
  | none => 0
  | some _ => GeneralPaperEndpointFractionConstructionStorage.window model W Q hQ c

def price (W P E : ℕ) : ℕ := P+E+64*W

def metadataCap (W T m K P E : ℕ) : ℕ := T+m+K+price W P E+1

def window {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) : ℕ :=
  let selected := child model W depth S H Q hQ hK classified proxyValue values columns
  let result := GeneralPaperRetainedCompilerPairBits.run model W depth S H Q hQ hK classified proxyValue values columns
  let endpoint := endpointWork model W Q hQ classified
  pairFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    GeneralPaperClassifierResultStorage.footprint W classified+rationalWordWidth proxyValue+optionFoot W result.1+
    endpointWindow model W Q hQ classified+activeWindow model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi+
    fields W [T,m,K,outer,inner,endpoint,selected.2,result.2,endpoint+selected.2,64*W,
      GeneralPaperFinalStaticLoopStorage.bit classified.choice.modify.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+160*W

def profile (W T m K R V F Proxy B E P EP : ℕ) : ℕ :=
  pairProfile W T m K R+GeneralPaperEncodedRationalRows.rowProfile W m V+F+Proxy+
    (pairProfile W T m K R+B+64*W+1)+E+B+
    12*(natBits (metadataCap W T m K P EP)+W)+192*W

theorem pair_bound {T m K : ℕ} (W R : ℕ) (columns : Columns T m K)
    (hr : ∀ j l,rationalWordWidth ((columns.rich.read j).anchors.read l)≤R)
    (hp : ∀ j l,rationalWordWidth ((columns.poor.read j).anchors.read l)≤R) :
    pairFoot W columns≤pairProfile W T m K R := by
  have hR := columns_bound W R columns.rich hr
  have hP := columns_bound W R columns.poor hp
  unfold pairFoot pairProfile
  omega

theorem returned {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) :
    optionFoot W (GeneralPaperRetainedCompilerPairBits.run model W depth S H Q hQ hK classified proxyValue values columns).1≤
      pairFoot W columns+activeWindow model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi+64*W+1 := by
  cases hc : classified.choice.modify with
  | none =>
    simp only [GeneralPaperRetainedCompilerPairBits.run,hc,activeWindow,optionFoot]
    omega
  | some side =>
    cases side with
    | rich =>
      have hOption : GeneralPaperRetainedModifiedColumnStorage.optionFoot W
          (GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.rich values 1 proxyValue false (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint).1≤
          GeneralPaperRetainedModifiedColumnStorage.window model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.rich values 1 proxyValue false (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint outer ho inner hi := by
        simp only [GeneralPaperRetainedModifiedColumnStorage.window]
        omega
      cases hr : (GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.rich values 1 proxyValue false (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint).1 with
      | none =>
        simp only [GeneralPaperRetainedCompilerPairBits.run,hc,hr,Option.map_none,optionFoot]
        omega
      | some r =>
        simp only [GeneralPaperRetainedCompilerPairBits.run,hc,hr,Option.map_some,optionFoot]
        simp only [hr,GeneralPaperRetainedModifiedColumnStorage.optionFoot] at hOption
        simp only [activeWindow,hc,pairFoot]
        omega
    | poor =>
      have hOption : GeneralPaperRetainedModifiedColumnStorage.optionFoot W
          (GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.poor values proxyValue 1 true (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint).1≤
          GeneralPaperRetainedModifiedColumnStorage.window model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.poor values proxyValue 1 true (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint outer ho inner hi := by
        simp only [GeneralPaperRetainedModifiedColumnStorage.window]
        omega
      cases hr : (GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
        hK columns.poor values proxyValue 1 true (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified).1 classified.choice.endpoint).1 with
      | none =>
        simp only [GeneralPaperRetainedCompilerPairBits.run,hc,hr,Option.map_none,optionFoot]
        omega
      | some r =>
        simp only [GeneralPaperRetainedCompilerPairBits.run,hc,hr,Option.map_some,optionFoot]
        simp only [hr,GeneralPaperRetainedModifiedColumnStorage.optionFoot] at hOption
        simp only [activeWindow,hc,pairFoot]
        omega

theorem work_shape {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) :
    (GeneralPaperRetainedCompilerPairBits.run model W depth S H Q hQ hK classified proxyValue values columns).2=
      endpointWork model W Q hQ classified+(child model W depth S H Q hQ hK classified proxyValue values columns).2+64*W := by
  cases hc : classified.choice.modify with
  | none => simp only [GeneralPaperRetainedCompilerPairBits.run,endpointWork,child,hc];omega
  | some side => cases side <;> simp only [GeneralPaperRetainedCompilerPairBits.run,endpointWork,child,hc]

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) (R V F Proxy B E P EP : ℕ)
    (hRich : ∀ j l,rationalWordWidth ((columns.rich.read j).anchors.read l)≤R)
    (hPoor : ∀ j l,rationalWordWidth ((columns.poor.read j).anchors.read l)≤R)
    (hValues : ∀ j,RationalHeight (values.values.read j) V)
    (hClassifier : GeneralPaperClassifierResultStorage.footprint W classified≤F)
    (hProxy : rationalWordWidth proxyValue≤Proxy)
    (hChild : ∀ outer ho inner hi,activeWindow model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi≤B)
    (hEndpoint : endpointWindow model W Q hQ classified≤E)
    (hP : (child model W depth S H Q hQ hK classified proxyValue values columns).2≤P)
    (hEP : endpointWork model W Q hQ classified≤EP)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) :
    window model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi≤profile W T m K R V F Proxy B E P EP ∧
      (GeneralPaperRetainedCompilerPairBits.run model W depth S H Q hQ hK classified proxyValue values columns).2≤price W P EP := by
  let result := GeneralPaperRetainedCompilerPairBits.run model W depth S H Q hQ hK classified proxyValue values columns
  let selected := child model W depth S H Q hQ hK classified proxyValue values columns
  let endpoint := endpointWork model W Q hQ classified
  change selected.2≤P at hP
  change endpoint≤EP at hEP
  have hColumns := pair_bound W R columns hRich hPoor
  have hValue := GeneralPaperEncodedRationalRows.row_bound W V values.values hValues
  have hActive := hChild outer ho inner hi
  have hReturn := returned model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi
  change optionFoot W result.1≤pairFoot W columns+activeWindow model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi+64*W+1 at hReturn
  have hWork : result.2≤price W P EP := by
    dsimp only [result]
    rw [work_shape]
    change endpoint+selected.2+64*W≤P+EP+64*W
    omega
  have hb := GeneralPaperFinalStaticLoopStorage.bit_bound classified.choice.modify.isSome
  have hr := GeneralPaperFinalStaticLoopStorage.bit_bound result.1.isSome
  have hf := fields_bound W (natBits (metadataCap W T m K P EP))
    [T,m,K,outer,inner,endpoint,selected.2,result.2,endpoint+selected.2,64*W,
      GeneralPaperFinalStaticLoopStorage.bit classified.choice.modify.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price at *;omega)
  change fields W _≤12*(natBits (metadataCap W T m K P EP)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  unfold window profile
  change pairFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    GeneralPaperClassifierResultStorage.footprint W classified+rationalWordWidth proxyValue+optionFoot W result.1+
    endpointWindow model W Q hQ classified+activeWindow model W depth S H Q hQ hK classified proxyValue values columns outer ho inner hi+
    fields W [T,m,K,outer,inner,endpoint,selected.2,result.2,endpoint+selected.2,64*W,
      GeneralPaperFinalStaticLoopStorage.bit classified.choice.modify.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+160*W≤_
  omega

end Blotto.GeneralPaperRetainedCompilerPairStorage
