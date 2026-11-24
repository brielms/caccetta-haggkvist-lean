import checkpoints.shen_extension.SingleArcLocalSignExample

namespace LeanCH.BR.Closure.StrictMergeSignControl
open Finset SingleArcLocalSignExample

def bank {I : Type*} [DecidableEq I] (G : I→I→Bool) (V S : Finset I) : Finset I :=
  V.filter (fun y => ∀s∈S,G s y=true)

/-- A degree and pairwise intersection test for every unweighted merge.
If the common bank has one label, use its degree. With two or more, both
sides of the complete bipartite incidence have at most h labels. -/
theorem count {I : Type*} [DecidableEq I] {V : Finset I} {G : I→I→Bool} {q d h : ℕ}
    (degree : ∀y∈V,(V.filter (fun x => G x y)).card≤d)
    (pairOut : ∀a∈V,∀b∈V,a≠b → (V.filter (fun y => G a y && G b y)).card≤h)
    (pairIn : ∀a∈V,∀b∈V,a≠b → (V.filter (fun x => G x a && G x b)).card≤h)
    (one : d+q<V.card) (two : h+q*h<V.card)
    {S : Finset I} (sub : S⊆V) (size : 2≤S.card) (proper : S≠V) :
    S.card+q*(bank G V S).card<V.card := by
  let C := V.filter (fun y => ∀s∈S,G s y=true)
  change S.card+q*C.card<V.card
  by_cases empty : C=∅
  · rw [empty,card_empty,Nat.mul_zero,Nat.add_zero]
    exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)
  obtain ⟨y,yc⟩ := nonempty_iff_ne_empty.mpr empty
  have see {v} (vc : v∈C) (s) (ss : s∈S) : G s v=true := (mem_filter.mp vc).2 s ss
  by_cases single : C.card≤1
  · have ss : S⊆V.filter (fun x => G x y) := fun s hs => mem_filter.mpr ⟨sub hs,see yc s hs⟩
    have card := (card_le_card ss).trans (degree y (mem_filter.mp yc).1)
    exact (Nat.add_le_add card (by simpa using Nat.mul_le_mul_left q single)).trans_lt one
  obtain ⟨a,b,ac,bc,ab⟩ := one_lt_card_iff.mp (by omega : 1<C.card)
  obtain ⟨i,j,si,sj,ij⟩ := one_lt_card_iff.mp size
  have left : S⊆V.filter (fun x => G x a && G x b) := fun s hs =>
    mem_filter.mpr ⟨sub hs,by simp [see ac s hs,see bc s hs]⟩
  have right : C⊆V.filter (fun v => G i v && G j v) := fun v hv =>
    mem_filter.mpr ⟨(mem_filter.mp hv).1,by simp [see hv i si,see hv j sj]⟩
  exact (Nat.add_le_add ((card_le_card left).trans (pairIn a (mem_filter.mp ac).1 b (mem_filter.mp bc).1 ab))
    (Nat.mul_le_mul_left q ((card_le_card right).trans (pairOut i (sub si) j (sub sj) ij)))).trans_lt two

set_option maxHeartbeats 2000000 in
private theorem intersections (G : Label→Label→Bool)
    (which : G=E ∨ G=(fun i j => E j i) ∨ G=child ∨ G=(fun i j => child j i)) :
      (∀y∈(univ : Finset Label),(univ.filter (fun x => G x y)).card≤4) ∧
      (∀i∈(univ : Finset Label),∀j∈(univ : Finset Label),i≠j → (univ.filter (fun y => G i y && G j y)).card≤2) ∧
      (∀i∈(univ : Finset Label),∀j∈(univ : Finset Label),i≠j → (univ.filter (fun x => G x i && G x j)).card≤2) := by
  rcases which with rfl|rfl|rfl|rfl <;> decide +kernel

private theorem scale {s c : ℕ} (h : s+3*c<10) :
    (s:ℝ)*(1/10)+3*((c:ℝ)*(1/10))<1 := by
  have realBound : (s:ℝ)+3*(c:ℝ)<10 := by exact_mod_cast h
  linarith only [realBound]

/-- Both old and inserted tables, and both orientations. The weights on
all four tables are the same old flat weights. -/
theorem all_bounds (G : Label→Label→Bool)
    (which : G=E ∨ G=(fun i j => E j i) ∨ G=child ∨ G=(fun i j => child j i))
    (S : Finset Label) (size : 2≤S.card) (proper : S≠univ) :
    (∑s∈S,weight s)+3*(∑y∈bank G univ S,weight y)<1 := by
  have data := intersections G which
  have bound := count (G:=G) (q:=3) (d:=4) (h:=2) data.1 data.2.1 data.2.2
    (by decide) (by decide) (subset_univ S) size proper
  simp only [weight,sum_const,nsmul_eq_mul]
  exact scale (lt_of_lt_of_eq bound (show (univ : Finset Label).card=10 by decide))

theorem positive_with_strict_merges :
    (∀G : Label→Label→Bool, (G=E ∨ G=(fun i j => E j i) ∨ G=child ∨ G=(fun i j => child j i)) →
      ∀S : Finset Label,2≤S.card → S≠univ →
      (∑s∈S,weight s)+3*(∑y∈bank G univ S,weight y)<1) ∧
    (∀v k : Label,0<SharedArcFlatResponse.test R⁻¹ weight weight 3 3 2 v k) :=
  ⟨all_bounds,fun v k => lt_of_lt_of_le (by norm_num : (0:ℝ)<1349/387800) (minimum.1 v k)⟩

end LeanCH.BR.Closure.StrictMergeSignControl
#print axioms LeanCH.BR.Closure.StrictMergeSignControl.positive_with_strict_merges
