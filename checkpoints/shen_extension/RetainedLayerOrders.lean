import checkpoints.shen_extension.RetainedLayerCapacity


namespace LeanCH.BR.RetainedLayerCapacity
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity RetainedRadiusLayers GuardedLayerGrowth

/-- A high row retains a score at radii three and four, with the minimum
degree and the high row threshold as separate parameters. -/
theorem high_score {D W q x d k} (free : QFree D W q) (hq : 5 ≤ q)
    (ld : 2 ≤ d) (cut : k ≤ q) (room : 2*d ≤ k+1) (growth : k+3*d ≤ 2*q+2)
    (rank : ∀x∈W,d ≤ (outN D W x).card) (xw : x∈W) (high : k+1 ≤ (outN D W x).card) :
    (k+2*d+1)+(k+3*d) ≤ (ball D W x 3).card+(ball D W x 4).card := by
  have first := high_row_ball_three_min ld room (free.mono_bound cut) rank xw high
  have last := PrefixDegreeGrowth.raise_floor (j:=3) (target:=k+3*d) free xw
    (by omega) rank hq first (by omega) (by
      intro m lo hi
      exact ⟨2,by decide,by decide,by omega,by omega⟩)
  change k+3*d ≤ (ball D W x 4).card at last
  omega

attribute [aesop safe forward (immediate := [free,hq,ld,cut,room,growth,rank,xw,high])
  (rule_sets := [CHGraphFamilies])] high_score


/-- Scores for degrees two and three come from the established ball bounds.
Only the radii three and four are fixed here. -/
private theorem rank_two {D W q} (free : QFree D W q) (hq : 4≤q)
    (rank : ∀x∈W,2≤(outN D W x).card) (x) (xw : x∈W) :
    16≤(ball D W x 3).card+(ball D W x 4).card := by
  have all := ball_growth q (by omega) D W free rank x xw
  have := all 3 (by omega)
  have := all 4 (by omega)
  omega

private theorem rank_three {D W q} (free : QFree D W q) (hq : 5≤q)
    (rank : ∀x∈W,3≤(outN D W x).card) (x) (xw : x∈W) :
    23≤(ball D W x 3).card+(ball D W x 4).card := by
  have a := ball_of_min (BRq3.ball_all 4 (by decide)) (free.mono_bound (by omega)) rank x xw
  have b := ball_of_min (BRq3.ball_all 5 (by decide)) (free.mono_bound hq) rank x xw
  change 10≤(ball D W x 3).card at a
  change 13≤(ball D W x 4).card at b
  omega

/-- The small-second-layer argument works across degrees. In the next
second-layer size the retained carrier has twice the degree in vertices,
half of them full. Compare its actual score with its pair capacity. -/
theorem diagonal_third {D V q r v k} (free : QFree D V q) (root : v∈V)
    (reg : OutEq r D V) (hq : 7 ≤ q) (hr : 4 ≤ r) (fits : r ≤ q+1)
    (time : k+2 ≤ q) (light : r < 2*k+3)
    (capacity : (2*r)*(2*r+1) < r*16+r*(2*r+9)) :
    3*r ≤ (ball D V v 3).card := by
  have f4 : 4 ≤ q := by omega
  have deg x (xm : x∈V) := (reg x xm).ge
  have sec := second_floor free f4 reg (by omega : 0<r) (by omega) root
  have bn := card_B1 (free.mono_bound f4) root
  have dr := reg v root
  by_cases low : (ball D V v 2).card=2*r
  · have sz := low
    rw [card_B2,bn,dr] at sz
    have short : (N2 D V v).card+1=r := by omega
    have no := no_return (k:=k) free f4 root reg (by omega) short time (by omega) light
    obtain ⟨_,_,_,last⟩ := sink_expansion free f4 root deg (card_pos.mp (by omega)) (by omega) no
    rw [card_B3,low]
    omega
  by_cases mid : (ball D V v 2).card=2*r+1
  · by_contra! small
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
    have cap := prefix_capacity (a:=1) (i:=3) (j:=4) (high:=2*r+9) free root (by omega) (by omega) deg
      (show 2+(ball D V v 3 \ ball D V v 2).card ≤ r by omega)
      (fun _ ff rr x xm=>rank_two ff (by omega) rr x xm)
      (fun _ ff rr x xm hx=>by
        have score := high_score (k:=r-1) ff (by omega) (by decide : 2≤2) (by omega) (by omega)
          (by omega) rr xm (show r-1+1≤_ by omega)
        omega)
    dsimp only at cap
    simp only [card_erase_of_mem (self_mem_ball root),mid,bn,dr,Nat.add_sub_cancel] at cap
    rw [show 2*r-r=r by omega] at cap
    omega
  apply PrefixDegreeGrowth.raise_floor (j:=2) (lo:=2*r+2) free root (by omega) deg (by omega) (by omega) (by omega)
  intro m lo hi
  by_cases first : m ≤ 3*q+1
  · exact ⟨3,by decide,by decide,by omega,by omega⟩
  · exact ⟨4,by decide,by decide,by omega,by omega⟩

attribute [aesop safe forward (immediate := [free,root,reg,hq,hr,fits,time,light,capacity])
  (rule_sets := [CHGraphFamilies])] diagonal_third

/-- The three arithmetic tests compare the fragment's pair capacity with
the costs of its marked layers. The universal bounds range only over
possible sizes of the second ball. -/
def FourthRoom (r : ℕ) : Prop :=
  (2*r)*(2*r+1)<r*16+r*(2*r+9) ∧
  (∀a∈Finset.Icc (2*r-1) (3*r-1),
    (3*r-1)*(3*r)<(3*r-1-a)*16+(a-r)*(2*r+9)+r*(4*r)) ∧
  (∀a∈Finset.Icc (2*r-1) (3*r),
    (3*r)*(3*r+1)<a*(2*r+14)+(3*r-a)*23)

instance (r) : Decidable (FourthRoom r) := by unfold FourthRoom; infer_instance

theorem diagonal_fourth {D V q r v} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (room : FourthRoom r) (reg : OutEq r D V) (root : v∈V) :
    4*r-1≤(ball D V v 4).card := by
  obtain ⟨middle,small,larger⟩ := room
  have deg x (xm : x∈V) := (reg x xm).ge
  have b3 := diagonal_third (k:=q-2) free root reg hq (by omega) fit (by omega) (by omega) middle
  have sec x (xm : x∈V) := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) xm
  have b2 := sec v root
  have bn := card_B1 (free.mono_bound (by omega : 4≤q)) root
  have dr := reg v root
  by_contra! tiny
  have mono := ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 3≤4)
  have diff := card_sdiff_add_card_eq_card mono
  have upper := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
  by_cases low : (ball D V v 3).card=3*r
  · have cap := prefix_three_scores (k:=3) (a:=2) (b:=1) (j:=2) (i:=3) (l:=4)
      (h:=2*r) (near:=4*r) (base:=16) (high:=2*r+9) free root (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) deg
      (show 2+(ball D V v 4 \ ball D V v 3).card ≤ r by omega)
      (fun x xm=>sec x (ball_subset (mem_of_mem_erase xm))) (by omega) (fun _ ff rr x xm=>by
        refine ⟨rank_two ff (by omega) rr x xm,?_⟩
        intro hx
        have h := high_score (k:=r-1) ff (by omega) (by decide : 2≤2) (by omega)
          (by omega) (by omega) rr xm (show r-1+1≤_ by omega)
        omega)
    dsimp only at cap
    simp only [card_erase_of_mem (self_mem_ball root),low,bn,dr,Nat.add_sub_cancel] at cap
    rw [Nat.sub_add_cancel (by omega : 1≤3*r)] at cap
    have fail := small ((ball D V v 2).card-1) (mem_Icc.mpr ⟨by omega,by omega⟩)
    omega
  by_cases mid : (ball D V v 3).card=3*r+1
  · have cap := prefix_capacity (a:=2) (i:=3) (j:=4) (base:=23) (high:=2*r+14) free root
      (by omega) (by omega) deg (show 3+(ball D V v 4 \ ball D V v 3).card≤r by omega)
      (fun _ ff rr=>rank_three ff (by omega) rr) (fun _ ff rr x xm hx=>by
        have h := high_score (k:=r-1) ff (by omega) (by decide : 2≤3) (by omega)
          (by omega) (by omega) rr xm (show r-1+1≤_ by omega)
        omega)
    dsimp only at cap
    simp only [card_erase_of_mem (self_mem_ball root),mid,Nat.add_sub_cancel] at cap
    have fail := larger ((ball D V v 2).card-1) (mem_Icc.mpr ⟨by omega,by omega⟩)
    omega
  have grow := PrefixDegreeGrowth.raise_floor (j:=3) (lo:=3*r+2) (target:=4*r-1) free root
    (by omega) deg (by omega) (by omega) (by omega) (by
      intro m lo hi
      by_cases first : m ≤ 4*q+1
      · exact ⟨4,by decide,by decide,by omega,by omega⟩
      · exact ⟨5,by decide,by decide,by omega,by omega⟩)
  change 4*r-1≤(ball D V v 4).card at grow
  omega

theorem diagonal_order {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (room : FourthRoom r) (live : V.Nonempty) (degree : ∀x∈V,r≤(outN D V x).card) :
    7*r-2≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have cap := card_ge_of_two_balls ff (by omega : 3+4≤q)
    (fun _ xm=>diagonal_third (k:=q-2) ff xm reg hq (by omega) fit (by omega) (by omega) room.1)
    (fun _ xm=>diagonal_fourth ff hq hr fit room reg xm) live
  omega

attribute [aesop safe forward (immediate := [free,hq,hr,fit,room,reg,root])
  (rule_sets := [CHGraphFamilies])] diagonal_fourth


/-- At a tight symmetric radius budget every third ball is the same size.
If that forces every second ball to be minimal, the tall successor of the
same root contradicts equality. -/
theorem two_radius_escape {D V q r b v} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (root : v∈V) (hr : 2≤r) (room : r≤2*q)
    (time : 3+3≤q) (third : ∀x∈V,b≤(ball D V x 3).card)
    (tight : ∀x∈V,(ball D V x 3).card=b → (ball D V x 2).card=2*r)
    (next : 3*r≤b+2) : 2*b≤V.card := by
  rw [two_mul]
  apply strict_order free ⟨v,root⟩ time third third
  intro u um eq
  have sm := tight u um eq
  have bank := sm
  rw [card_B2,card_B1 (free.mono_bound hq) um,reg u um] at bank
  have top := eq
  rw [card_B3,sm] at top
  obtain ⟨w,wm,tall,_⟩ := OneSpareGrowth.tall_successor free hq um reg hr room (by omega) (by omega)
  have hv := outN_subset wm
  exact ⟨w,hv,lt_of_le_of_ne (third w hv) (fun e=> (Nat.ne_of_gt tall) (tight w hv e.symm))⟩

attribute [aesop safe forward (immediate := [free,hq,reg,root,hr,room,time,third,tight,next])
  (rule_sets := [CHGraphFamilies])] two_radius_escape

/-- When the third ball is small, a second ball of size 2r+1
would retain degree two and all the first heads. A larger second ball
contradicts the small-rank growth bounds. -/
theorem tight_second {D V q r k v} (free : QFree D V q) (hq : 6≤q) (hr : 3≤r)
    (kq : k≤q) (rk : k+1≤r) (kk : 4≤k+1) (room : r≤2*q)
    (mid : (2*r)*(2*r+1)<r*(2*(k+5))+r*14)
    (_range3 : 2*r+2≤3*q+1) (range4 : 3*r≤4*q+2)
    (reg : OutEq r D V) (root : v∈V) (low : (ball D V v 3).card≤3*r-1) :
    (ball D V v 2).card=2*r := by
  have deg x (xm : x∈V) := (reg x xm).ge
  have sec := second_floor free (by omega : 4≤q) reg (by omega : 0<r) room root
  have bn := card_B1 (free.mono_bound (by omega : 4≤q)) root
  have dr := reg v root
  by_contra ne
  by_cases small : (ball D V v 2).card=2*r+1
  · have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
    have cap := prefix_capacity (a:=1) (i:=3) (j:=3) (base:=14) (high:=2*(k+5))
      free root (by omega) (by omega) deg (show 2+(ball D V v 3 \ ball D V v 2).card≤r by omega)
      (fun _ ff rr x xm=> by
        have row := ball_growth q (by omega) _ _ ff rr x xm 3 (by omega)
        omega)
      (fun _ ff rr x xm hx=> by
        have row := high_row_ball_three_min (by decide : 2≤2) kk (ff.mono_bound kq) rr xm (rk.trans hx)
        omega)
    dsimp only at cap
    simp only [card_erase_of_mem (self_mem_ball root),small,bn,dr,Nat.add_sub_cancel] at cap
    rw [show 2*r-r=r by omega] at cap
    omega
  have grow := PrefixDegreeGrowth.raise_floor (j:=2) (lo:=2*r+2) (target:=3*r) free root
    (by omega) deg (by omega) (by omega) (by omega) (by
      intro m lo hi
      by_cases fit : m≤3*q+1
      · exact ⟨3,by decide,by decide,by omega,by omega⟩
      · exact ⟨4,by decide,by decide,by omega,by omega⟩)
  change 3*r≤(ball D V v 3).card at grow
  omega

def SymmetricRoom (r q : ℕ) : Prop :=
  6≤q ∧ 4≤r ∧ r≤2*q ∧ 2*r+2≤3*q+1 ∧ 3*r≤4*q+2 ∧ r<2*(q-2)+3 ∧
    (2*r)*(2*r+1)<r*(2*(min q (r-1)+5))+r*14

instance (r q) : Decidable (SymmetricRoom r q) := by unfold SymmetricRoom; infer_instance

theorem symmetric_shape {D V q r v} (free : QFree D V q) (reg : OutEq r D V)
    (root : v∈V) (room : SymmetricRoom r q) :
    3*r-1≤(ball D V v 3).card ∧ ((ball D V v 3).card≤3*r-1 → (ball D V v 2).card=2*r) := by
  obtain ⟨hq,hr,rq,r3,r4,guard,cap⟩ := room
  have k := min_le_right q (r-1)
  have kk : 4≤min q (r-1)+1 := by omega
  have tight := tight_second free hq (by omega) (min_le_left q (r-1)) (by omega) kk rq cap r3 r4 reg root
  refine ⟨?_,tight⟩
  by_contra! small
  have t := tight (by omega)
  have first := t
  rw [card_B2,card_B1 (free.mono_bound (by omega : 4≤q)) root,reg v root] at first
  have z := GuardedLayerGrowth.guarded_third (k:=q-2) free (by omega) root reg (by omega)
    (by omega) (by omega) rq guard
  rw [card_B3,t] at small
  omega

theorem symmetric_order {D V q r} (free : QFree D V q) (room : SymmetricRoom r q)
    (live : V.Nonempty) (degree : ∀x∈V,r≤(outN D V x).card) : 6*r-2≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have shape x (xm : x∈V) := symmetric_shape ff reg xm room
  obtain ⟨u,um⟩ := live
  obtain ⟨hq,hr,rq,_⟩ := room
  have cap := two_radius_escape ff (by omega) reg um (by omega) rq (by omega)
    (fun _ xm=>(shape _ xm).1) (fun _ xm eq=>(shape _ xm).2 eq.le) (by omega)
  omega

attribute [aesop safe forward (immediate := [free,hq,hr,kq,rk,kk,room,mid,_range3,range4,reg,root,low])
  (rule_sets := [CHGraphFamilies])] tight_second
attribute [aesop safe forward (immediate := [free,reg,root,room])
  (rule_sets := [CHGraphFamilies])] symmetric_shape

#print axioms high_score
#print axioms diagonal_third
#print axioms diagonal_fourth
#print axioms diagonal_order
#print axioms two_radius_escape
#print axioms tight_second
#print axioms symmetric_shape
#print axioms symmetric_order

end LeanCH.BR.RetainedLayerCapacity
