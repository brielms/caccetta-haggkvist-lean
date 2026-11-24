import checkpoints.shen_extension.SharedHeadEndpoints

namespace LeanCH.BR.ShenSharedHead
open BRq2 BRq3 BR45
open Classical

/-- The internal degree at a common head and the distinct new endpoints
together pay for the common bank. This holds separately at each head. -/
theorem bank_payment {D : CH.Digraph} {V : Finset ℕ} {u v w s}
    (hm : OutEq s D V) (hv : v∈V) (hw : w∈commonOut D V u v) :
    (commonOut D V u v).card≤(endpoints D V u v).card+(outN D (commonOut D V u v) w).card := by
  let T := commonOut D V u v
  have tv : T⊆outN D V v := Finset.inter_subset_right
  have cover : outN D V w⊆outN D T w ∪ ((outN D V v \ T) ∪ endpoints D V u v) := by
    intro y hy
    by_cases yt : y∈T
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨yt,(mem_outN.mp hy).2⟩)
    by_cases h : y∈outN D V v
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h,yt⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(mem_outN.mp hy).1,h,w,hw,(mem_outN.mp hy).2⟩))
  have pay := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have := Finset.card_union_le (outN D V v \ T) (endpoints D V u v)
  have width := Finset.card_sdiff_add_card_eq_card tv
  rw [hm v hv] at width
  rw [hm w (mem_outN.mp (tv hw)).1] at pay
  change T.card≤_+(outN D T w).card
  omega

/-- Feed an arbitrary local linear degree bound into the exact endpoint
count. The vertex v itself supplies one additional unit on each arc. -/
theorem endpoint_feedback {D : CH.Digraph} {V : Finset ℕ} {s a b}
    (hf : QFree D V 3) (hm : OutEq s D V) (ne : V.Nonempty) (hs : 0<s)
    (light : ∀ u∈V,∀ v∈outN D V u,let T := commonOut D V u v
      T.Nonempty → ∃ w∈T,a*(outN D T w).card≤b*T.card) :
    2*a*(3*s+1)+b≤2*a*V.card+b*s := by
  let t := fun u v => (commonOut D V u v).card
  let c := fun u v => (endpoints D V u v).card
  let N := V.card*s
  have one (u) (hu : u∈V) (v) (hv : v∈outN D V u) : a*t u v≤a*c u v+b*t u v := by
    by_cases h : (commonOut D V u v).Nonempty
    · obtain ⟨w,hw,le⟩ := light u hu v hv h
      have pay := Nat.mul_le_mul_left a (bank_payment hm (mem_outN.mp hv).1 hw)
      dsimp only [t,c]
      nlinarith only [pay,le]
    · simp [t,Finset.not_nonempty_iff_eq_empty.mp h]
  have sum := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (one u hu))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at sum
  change a*edges D V t≤a*edges D V c+b*edges D V t at sum
  have budget : N*(3*s+1)+edges D V c≤N*V.card+edges D V t := endpoint_balance hf hm
  have limit : 2*edges D V t+N≤N*s := common_head_capacity hf hm
  have scaled := Nat.mul_le_mul_left a budget
  have weighted := Nat.mul_le_mul_left b limit
  have pos : 0<N := Nat.mul_pos (Finset.card_pos.mpr ne) hs
  apply Nat.le_of_mul_le_mul_left _ pos
  nlinarith only [scaled,weighted,sum]

theorem cycle_of_ratio_plus_one {D : CH.Digraph} {n s a b}
    (hb : 0<b) (ratio : 2*a*a+b*b≤6*a*b) (hn : 0<n) (hs : 0<s)
    (ord : b*n≤a*s+b) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  let V := Finset.range n
  have deg (x) (hx : x∈V) := Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)
  obtain ⟨F,sub,reg⟩ := exists_outEq deg
  have free := qfree_sub sub (qfree_of_noShort hl no)
  have cap := endpoint_feedback free reg ⟨0,Finset.mem_range.mpr hn⟩ hs (a:=a) (b:=b) (by
    intro u _ v _ T ne
    obtain ⟨w,hw,lo⟩ := T.exists_min_image (fun z => (outN F T z).card) ne
    have tv : T⊆V := Finset.inter_subset_left.trans (Finset.filter_subset _ _)
    exact ⟨w,hw,(order_bound hb ratio (free.mono_set tv) lo ne).le⟩)
  change 2*a*(3*s+1)+b≤2*a*(Finset.range n).card+b*s at cap
  rw [Finset.card_range] at cap
  have bound := Nat.mul_le_mul_left b cap
  have poly := Nat.mul_le_mul_right s ratio
  have upper := Nat.mul_le_mul_left (2*a) ord
  nlinarith only [bound,poly,upper,Nat.mul_pos hb hb]

#print axioms endpoint_feedback
#print axioms cycle_of_ratio_plus_one

end LeanCH.BR.ShenSharedHead
