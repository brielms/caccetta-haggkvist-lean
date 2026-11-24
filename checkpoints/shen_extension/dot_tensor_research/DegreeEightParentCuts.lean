import checkpoints.shen_extension.ParentCutPacking
import checkpoints.shen_extension.PrefixDegreeGrowth
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightPairCover_20261121
import checkpoints.shen_extension.dot_tensor_research.DegreeSevenVerified_20261121

namespace LeanCH.BR.ParentCutPacking
open Finset BRq2 BRq3 BR45 BRsGen

theorem parent_cut_size {D V q a k r s} (free : QFree D V q) (av : a∈V)
    (dist : k+2≤q) (deg : ∀v∈V,(outN D V v).card≤r)
    (pairs : ∀x∈V,∀y∈V,x≠y → ∃v∈V,D v x=true ∧ D v y=true)
    (parents : s≤(inN D V a).card) :
    s*(V.card-s)≤(V.card-(ball D V a k).card)*(r*r/4) := by
  obtain ⟨S,sub,sz⟩ := exists_subset_card_eq parents
  have sv : S⊆V := fun _ h=>(mem_inN.mp (sub h)).1
  have cross := cross_capacity (outN D V) (fun v hv=>deg v (mem_sdiff.mp hv).1)
    (covers_outside_ball free av dist sub pairs)
  simpa only [card_sdiff_of_subset sv,card_sdiff_of_subset ball_subset,sz] using cross

theorem regular_slot_bill {D V q a r k h} (free : QFree D V q) (av : a∈V)
    (dist : k+2≤q) (deg : OutEq r D V) (reg : ∀x∈V,(inN D V x).card=r)
    (pairs : ∀x∈V,∀y∈V,x≠y → ∃v∈V,D v x=true ∧ D v y=true)
    (room : (h-1)*(r-1)<r) :
    r*r + (V.card-r)*h ≤ (V.card-(ball D V a k).card)*r := by
  classical
  let S := inN D V a
  let R := V\ball D V a k
  have sub : S⊆V := fun _ xm=>(mem_inN.mp xm).1
  have cnt : S.card=r := reg a av
  have cover := covers_outside_ball free av dist (Subset.rfl : S⊆inN D V a) pairs
  have degree v (vm : v∈R) := (deg v (mem_sdiff.mp vm).1).le
  have all (x) (xs : x∈S) : R.filter (fun v=>x∈outN D V v) = inN D V x := by
    ext v
    exact ⟨fun f=>mem_inN.mpr ⟨(mem_sdiff.mp (mem_filter.mp f).1).1,
      (mem_outN.mp (mem_filter.mp f).2).2⟩,fun f=> mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨(mem_inN.mp f).1,parent_outside free av dist xs (mem_inN.mp f).2⟩,
       mem_outN.mpr ⟨sub xs,(mem_inN.mp f).2⟩⟩⟩
  have bill := incidence_capacity (outN D V) sub degree
    (fun x xs=>show r≤_ by rw [all x xs,reg x (sub xs)])
    (outside_multiplicity (outN D V) degree cover (by rwa [cnt]))
  simpa only [R,card_sdiff_of_subset sub,card_sdiff_of_subset ball_subset,cnt] using bill

/-- A numerical certificate for the very next growth step. Bounds for other
degrees or cutoffs can call the same arbitrary-rank theorem. -/
private theorem three_floor {D V q a} (free : QFree D V q) (av : a∈V)
    (q5 : 5≤q) (degree : OutEq 8 D V) : 22≤(ball D V a 3).card := by
  have hm v (vm : v∈V) := (degree v vm).ge
  have one : (ball D V a 1).card=9 := by
    rw [card_B1 (free.mono_bound (by omega : 4≤q)) av,degree a av]
  have two : 16≤(ball D V a 2).card := by
    apply PrefixDegreeGrowth.raise_floor (j:=1) free av (by omega) hm q5 one.ge (by decide)
    intro m low high
    by_cases fit : m≤11
    · exact ⟨2,by decide,by decide,by omega,by omega⟩
    · exact ⟨3,by decide,by decide,by omega,by omega⟩
  apply PrefixDegreeGrowth.raise_floor (j:=2) free av (by omega) hm q5 two (by decide)
  intro m low high
  by_cases eq : m=16
  · exact ⟨3,by decide,by decide,by omega,by omega⟩
  by_cases fit : m≤21
  · exact ⟨4,by decide,by decide,by omega,by omega⟩
  · omega

theorem order44 {D V} (free : QFree D V 6) (size : V.card=44)
    (hm : ∀v∈V,8≤(outN D V v).card) : False := by
  classical
  obtain ⟨G,sub,reg⟩ := exists_outEq hm
  have hf := qfree_sub sub free
  have ne : V.Nonempty := card_pos.mp (by omega)
  have pairs := DotDegreeEight.pair_cover_of_endpoint DotDegreeSeven.endpoint_six_seven
    (by decide) (by decide) hf (by simpa using size) reg
  have total := sum_out_in G V
  have high : ∃a∈V,8≤(inN G V a).card := by
    by_contra! low
    have lt := sum_lt_sum_of_nonempty ne low
    rw [←total,sum_congr rfl reg] at lt
    omega
  obtain ⟨a,av,parents⟩ := high
  have three := three_floor hf av (by decide) reg
  have four : 27≤(ball G V a 4).card := by
    apply PrefixDegreeGrowth.raise_floor (j:=3) hf av (by decide) (fun v hv=>(reg v hv).ge)
      (by decide) three (by decide)
    intro m low high
    by_cases fit : m≤25
    · exact ⟨4,by decide,by decide,by omega,by omega⟩
    · exact ⟨5,by decide,by decide,by omega,by omega⟩
  have cap := parent_cut_size hf av (k:=4) (by decide) (fun v hv=>(reg v hv).le) pairs parents
  rw [size] at cap
  omega

theorem order37 {D V} (free : QFree D V 5) (size : V.card=37)
    (hm : ∀v∈V,8≤(outN D V v).card) : False := by
  classical
  obtain ⟨G,sub,reg⟩ := exists_outEq hm
  have hf := qfree_sub sub free
  have pairs := DotDegreeEight.pair_cover_of_endpoint DotDegreeSevenLow.endpoint_five_seven
    (by decide) (by decide) hf (by simpa using size) reg
  have floor a (av : a∈V) := three_floor hf av (by decide) reg
  have upper a (av : a∈V) : (inN G V a).card≤8 := by
    by_contra! big
    have cap := parent_cut_size hf av (k:=3) (by decide) (fun v hv=>(reg v hv).le) pairs
      (show 9≤(inN G V a).card by omega)
    rw [size] at cap
    have := floor a av
    omega
  have total : (∑x∈V,(inN G V x).card)=(∑_x∈V,8) := by rw [←sum_out_in,sum_congr rfl reg]
  have eq := (sum_eq_sum_iff_of_le upper).mp total
  obtain ⟨a,av⟩ := (card_pos.mp (by omega : 0<V.card))
  have cap := regular_slot_bill (k:=3) (h:=2) hf av (by decide) reg eq pairs (by decide)
  rw [size] at cap
  have := floor a av
  omega

#print axioms parent_cut_size
#print axioms regular_slot_bill
#print axioms order37
#print axioms order44
end LeanCH.BR.ParentCutPacking
