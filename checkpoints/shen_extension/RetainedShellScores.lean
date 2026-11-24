import checkpoints.shen_extension.CyclePrefixGrowth
import checkpoints.shen_extension.FullRowEscape
namespace LeanCH.BR.RetainedShellScores
open Finset BRq2 BRq3 BR45 BRsGen RetainedRadiusLayers RetainedMixedCapacity

/-- Iterate a retained rank on the actual ball, up to its order bound. -/
theorem iterate {D V q x j k b d} (free : QFree D V q) (xm : x∈V)
    (rank : ∀v∈V,d≤(outN D V v).card) (hq : 5≤q) (low : 2≤d) (high : d≤5)
    (time : j+k≤q) (cap : b+k≤q*d+2) (positive : 1<b) (start : b≤(ball D V x j).card) :
    b+k≤(ball D V x (j+k)).card := by
  induction k with
  | zero => simpa using start
  | succ k ih =>
    apply PrefixDegreeGrowth.raise_floor (lo:=b+k) free xm time rank hq (ih (by omega) (by omega)) (by omega)
    intro m lo hi
    exact ⟨d,low,high,by omega,by omega⟩

/-- A full row, one retaining a second ball, and one retaining a third
ball are nested on the same carrier. Each label earns only the increment
for its strongest retained radius. -/
def load (s r m a b c : ℕ) : ℕ :=
  2*(m*(2*s+1)+a*(r-s)+b*(r-2)+c*(r+2-s))

theorem increments {α : Type*} [DecidableEq α] {W A B C : Finset α}
    {f : α→ℕ} {n i j k : ℕ} (aw : A⊆W) (ba : B⊆A) (cb : C⊆B)
    (s0 : ∀x∈W,n≤f x) (s1 : ∀x∈A,n+i≤f x)
    (s2 : ∀x∈B,n+i+j≤f x) (s3 : ∀x∈C,n+i+j+k≤f x) :
    W.card*n+A.card*i+B.card*j+C.card*k≤∑x∈W,f x := by
  have h0 := sum_le_sum (s:=W\A) (fun x hx=>s0 x (mem_sdiff.mp hx).1)
  have h1 := sum_le_sum (s:=A\B) (fun x hx=>s1 x (mem_sdiff.mp hx).1)
  have h2 := sum_le_sum (s:=B\C) (fun x hx=>s2 x (mem_sdiff.mp hx).1)
  have h3 := sum_le_sum s3
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset aw] at h0
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset ba] at h1
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset cb] at h2
  rw [sum_const_nat (fun _ _=>rfl)] at h3
  have hA := card_le_card aw
  have hB := card_le_card ba
  have hC := card_le_card cb
  have := sum_sdiff aw (f:=f)
  have := sum_sdiff ba (f:=f)
  have := sum_sdiff cb (f:=f)
  let u := W.card-A.card
  let v := A.card-B.card
  let w := B.card-C.card
  have uu : W.card = u+A.card := (Nat.sub_add_cancel hA).symm
  have vv : A.card = v+B.card := (Nat.sub_add_cancel hB).symm
  have ww : B.card = w+C.card := (Nat.sub_add_cancel hC).symm
  change u*n ≤ _ at h0
  change v*(n+i) ≤ _ at h1
  change w*(n+i+j) ≤ _ at h2
  rw [uu,vv,ww]
  nlinarith only [h0,h1,h2,h3,‹∑x∈W\A,f x + ∑x∈A,f x = _›,
    ‹∑x∈A\B,f x + ∑x∈B,f x = _›,‹∑x∈B\C,f x + ∑x∈C,f x = _›]

theorem load_mono {s r m a b c a' b' c'} (ha : a≤a') (hb : b≤b') (hc : c≤c') :
    load s r m a b c≤load s r m a' b' c' := by
  unfold load
  gcongr

theorem prefix_sum {D V q r s k u} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (time : k+4≤q) (radius : s≤q) (timeFloor : 5≤q)
    (rs : s≤r) (sr : 3≤s) (room : 2*r+s≤2*q+3)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card) (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (reserve : 2+(ball D V u (k+4)\ball D V u (k+3)).card≤r) :
    let L := fun j=>(ball D V u j).erase u
    (L (k+3)).card*(2*s+1)+(L (k+2)).card*(r-s)+(L (k+1)).card*(r-2)+(L k).card*(r+2-s) ≤
      ∑x∈L (k+3),(ball D (L (k+3)) x s).card := by
  classical
  let L := fun j=>(ball D V u j).erase u
  let W := L (k+3)
  let row := fun x=>(ball D W x s).card
  have nest {i j : ℕ} (le : i≤j) : L i⊆L j := erase_subset_erase _ (ball_mono_radius le)
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have ff := free.mono_set wv
  have rank := minOut_prefix_erase (d:=2) free uv time deg reserve
  have score := increments (f:=row) (n:=2*s+1) (i:=r-s) (j:=r-2) (k:=r+2-s)
    (nest (by omega : k+2≤k+3)) (nest (by omega : k+1≤k+2)) (nest (by omega : k≤k+1))
    (fun x xm=>by
      have := ball_growth q (by omega) D W ff rank x xm s (by omega)
      exact this) (fun x xm=>by
      have xw : x∈W := nest (by omega : k+2≤k+3) xm
      have high := (deg x (wv xw)).trans (card_le_card
        (outN_prefix_erase_root free uv (by omega : k+2+1≤q) (mem_of_mem_erase xm)))
      have b3 := FullRowEscape.high_third ff (by omega) rank xw high (by omega)
      have gain := iterate (j:=3) (k:=s-3) ff xw rank (by omega) (by decide) (by decide)
        (by omega) (by omega) (by omega) b3
      rw [show 3+(s-3)=s by omega] at gain
      dsimp only [row]
      omega) (fun x xm=>by
      have xw : x∈W := nest (by omega : k+1≤k+3) xm
      have b2 := second x (wv xw)
      rw [retained_ball free uv xm (show k+1+2≤k+3 by omega) (by omega)] at b2
      have gain := iterate (j:=2) (k:=s-2) ff xw rank (by omega) (by decide) (by decide)
        (by omega) (by omega) (by omega) b2
      rw [show 2+(s-2)=s by omega] at gain
      dsimp only [row]
      omega) (fun x xm=>by
      have b3 := third x (ball_subset (mem_of_mem_erase xm))
      rw [retained_ball free uv xm (show k+3≤k+3 by omega) (by omega)] at b3
      have use := b3.trans (card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=x) sr))
      dsimp only [row]
      omega)
  exact score

theorem prefix_load {D V q r s k u} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (time : k+4≤q) (radii : 2*s≤q)
    (rs : s≤r) (sr : 3≤s) (room : 2*r+s≤2*q+3)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card) (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (reserve : 2+(ball D V u (k+4)\ball D V u (k+3)).card≤r) :
    let L := fun j=>(ball D V u j).erase u
    load s r (L (k+3)).card (L (k+2)).card (L (k+1)).card (L k).card ≤
      (L (k+3)).card*((L (k+3)).card+1) := by
  let W := (ball D V u (k+3)).erase u
  let row := fun x=>(ball D W x s).card
  have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
  have score := prefix_sum free uv deg time (by omega : s≤q) (by omega) rs sr room second third reserve
  have cap := weighted_rows (i:=s) (j:=s) ff (by omega) (score:=fun x=>row x + row x) (fun _ _=>le_rfl)
  rw [sum_add_distrib] at cap
  dsimp only [load,W,row] at *
  omega

#print axioms prefix_sum
attribute [aesop safe forward (immediate := [free,xm,rank,hq,low,high,time,cap,positive,start])
  (rule_sets := [CHGraphFamilies])] iterate
attribute [aesop safe forward (immediate := [free,uv,deg,time,radii,rs,sr,room,second,third,reserve])
  (rule_sets := [CHGraphFamilies])] prefix_load
#print axioms iterate
#print axioms increments
#print axioms prefix_load
end LeanCH.BR.RetainedShellScores
