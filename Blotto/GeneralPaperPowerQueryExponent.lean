import Blotto.GeneralPaperPowerTableExponent

/-! Every selected product consumes its degree from the remaining query
budget. Centered exponents therefore depend on the requested exponent,
not on the sum of all columns or a factor of the mantissa precision.
-/
namespace Blotto.GeneralPaperPowerQueryExponent
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable GeneralPaperCenteredExponent
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem scan (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p) (entries : List Entry)
    (hNormal : ∀ e∈entries,Normal unit e.number) (hPositive : ∀ e∈entries,0<e.number.mantissa)
    (hBounds : ∀ e∈entries,Power p e.degree e.number) (remaining used : ℕ) (acc : Number)
    (hAcc : Normal unit acc) (hPos : 0<acc.mantissa)
    (hLower : -(used:ℤ)≤centered p acc) (hUpper : centered p acc≤0) :
    -((used+remaining:ℕ):ℤ)≤centered p (GeneralPaperRoundedPowerQuery.scan unit p entries remaining acc).number ∧
      centered p (GeneralPaperRoundedPowerQuery.scan unit p entries remaining acc).number≤0 := by
  induction entries generalizing remaining used acc with
  | nil =>
    change -((used+remaining:ℕ):ℤ)≤centered p acc ∧ centered p acc≤0
    push_cast
    constructor <;> omega
  | cons e rest ih =>
    have hn := hNormal e List.mem_cons_self
    have hp := hPositive e List.mem_cons_self
    have hb := hBounds e List.mem_cons_self
    have hRestN : ∀ a∈rest,Normal unit a.number := fun a ha => hNormal a (List.mem_cons_of_mem _ ha)
    have hRestP : ∀ a∈rest,0<a.number.mantissa := fun a ha => hPositive a (List.mem_cons_of_mem _ ha)
    have hRestB : ∀ a∈rest,Power p a.degree a.number := fun a ha => hBounds a (List.mem_cons_of_mem _ ha)
    rw [GeneralPaperRoundedPowerQuery.scan]
    split
    · rename_i hSelected
      have hm := GeneralPaperCenteredExponent.multiply unit p acc e.number hPos hp
      have hProductLower : -((used+e.degree:ℕ):ℤ)≤centered p (GeneralPaperDyadicMultiply.multiply unit p acc e.number).number := by
        have he := hb.1
        push_cast
        omega
      have hProductUpper : centered p (GeneralPaperDyadicMultiply.multiply unit p acc e.number).number≤0 := by
        have he := hb.2
        omega
      have hNorm := GeneralPaperDyadicMultiply.multiply_normal unit p (Nat.zero_lt_of_lt hUnit) hPower acc e.number hAcc hn
      have hPositive := GeneralPaperDyadicMultiply.multiply_positive unit p (Nat.zero_lt_of_lt hUnit) hPower acc e.number hAcc hn hPos hp
      have hi := ih hRestN hRestP hRestB (remaining-e.degree) (used+e.degree)
        (GeneralPaperDyadicMultiply.multiply unit p acc e.number).number hNorm hPositive hProductLower hProductUpper
      have hSum : used+e.degree+(remaining-e.degree)=used+remaining := by omega
      simpa only [hSum] using hi
    · exact ih hRestN hRestP hRestB remaining used acc hAcc hPos hLower hUpper

theorem constructed (lambda k exponent : ℕ) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    let out := GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) exponent;
    -(exponent:ℤ)≤centered f.fractionalBits out.number ∧ centered f.fractionalBits out.number≤0 := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
  let table := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b f.columns
  have hu := GeneralPaperPowerPrecision.unit_positive lambda k
  have hPower := GeneralPaperPowerPrecision.unit_power lambda k
  have hb := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k (Nat.zero_lt_of_lt hu) hPower
  have hGood := build_good f.unit f.fractionalBits hu hPower b hb.1 hb.2 f.columns
  have hExp := GeneralPaperPowerTableExponent.build f.unit f.fractionalBits hu hPower b hb.1 hb.2
    (stored_base f.unit f.fractionalBits k) f.columns
  have h := scan f.unit f.fractionalBits hu hPower table.entries
    (fun e he => (hGood.2 e he).2.1) (fun e he => (hGood.2 e he).2.2.1) hExp.2 exponent 0
    (one f.unit f.fractionalBits) (one_normal f.unit f.fractionalBits (Nat.zero_lt_of_lt hu))
    (by change 0<f.unit; exact Nat.zero_lt_of_lt hu)
    (by simp only [centered,one]; omega) (by simp only [centered,one]; omega)
  simpa only [GeneralPaperPreparedPowers.query,GeneralPaperPreparedPowers.prepare,
    GeneralPaperRoundedPowerQuery.evaluate,f,b,table,Nat.zero_add] using h

theorem magnitude (lambda k exponent : ℕ) :
    (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) exponent).number.exponent.natAbs≤
      exponent+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits := by
  have h := constructed lambda k exponent
  exact absolute_bound _ _ _ h.1 h.2

theorem query_prefix (lambda k exponent visited : ℕ) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    (GeneralPaperRoundedPowerQuery.scan f.unit f.fractionalBits (prepared.table.take visited) exponent
      (one f.unit f.fractionalBits)).number.exponent.natAbs≤exponent+f.fractionalBits := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
  let table := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b f.columns
  have hu := GeneralPaperPowerPrecision.unit_positive lambda k
  have hPower := GeneralPaperPowerPrecision.unit_power lambda k
  have hb := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k (Nat.zero_lt_of_lt hu) hPower
  have hGood := build_good f.unit f.fractionalBits hu hPower b hb.1 hb.2 f.columns
  have hExp := GeneralPaperPowerTableExponent.build f.unit f.fractionalBits hu hPower b hb.1 hb.2
    (stored_base f.unit f.fractionalBits k) f.columns
  have h := scan f.unit f.fractionalBits hu hPower (table.entries.take visited)
    (fun e he => (hGood.2 e (List.mem_of_mem_take he)).2.1)
    (fun e he => (hGood.2 e (List.mem_of_mem_take he)).2.2.1)
    (fun e he => hExp.2 e (List.mem_of_mem_take he)) exponent 0
    (one f.unit f.fractionalBits) (one_normal f.unit f.fractionalBits (Nat.zero_lt_of_lt hu))
    (by change 0<f.unit; exact Nat.zero_lt_of_lt hu)
    (by simp only [centered,one]; omega) (by simp only [centered,one]; omega)
  have hL : -(exponent:ℤ)≤centered f.fractionalBits
      (GeneralPaperRoundedPowerQuery.scan f.unit f.fractionalBits (table.entries.take visited) exponent
        (one f.unit f.fractionalBits)).number := by simpa only [Nat.zero_add] using h.1
  exact absolute_bound _ exponent _ hL h.2

theorem cached (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (exponent : ℕ)
    (hExponent : exponent≤c.controls.precision.levelBound) :
    (GeneralPaperCachedPowerQuery.query primitive W c exponent).1.number.exponent.natAbs≤
      c.controls.precision.levelBound+c.powers.format.fractionalBits := by
  rw [GeneralPaperCachedPowerQuery.data primitive W m lambda k Qv c hc]
  subst c
  exact (magnitude lambda k exponent).trans (Nat.add_le_add_right hExponent _)

end Blotto.GeneralPaperPowerQueryExponent
