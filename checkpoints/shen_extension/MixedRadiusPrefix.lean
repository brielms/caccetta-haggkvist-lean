import checkpoints.shen_extension.WidePrefixCapacity
namespace LeanCH.BR.MixedRadiusPrefix
open Finset BRq2 BRq3 BR45 BRsGen RetainedShellScores RetainedMixedCapacity

def score (s r m a b c : ℕ) : ℕ := m*(2*s+1)+a*(r-s)+b*(r-2)+c*(r+2-s)

def Room (q r i j a b c lo hi : ℕ) : Prop :=
  ∀m∈Icc lo hi, (∃d∈Icc 2 5,m≤q*d ∧ hi+d≤m+r) ∨
    (hi+2≤m+r ∧ m*(m+1)<score i r m a b c + score j r m a b c) ∨
    (hi+3≤m+r ∧ m*(m+1)<m*(3*(i+j)+2)+c*(6*r-3*(i+j)))
instance (q r i j a b c lo hi) : Decidable (Room q r i j a b c lo hi) := by unfold Room; infer_instance

/-- Use the same nested sets on both sides of the ordered-pair count.
The two radii can differ, so an odd cutoff can spend its last step. -/
theorem squeeze {D V q r i j k u a b c lo hi} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (time : k+4≤q) (radii : i+j≤q)
    (ir : i≤r) (jr : j≤r) (si : 3≤ i) (sj : 3≤j)
    (ri : 2*r+i≤2*q+3) (rj : 2*r+j≤2*q+3)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card) (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (tiny : (ball D V u (k+4)).card≤hi+1)
    (ha : a+1≤(ball D V u (k+2)).card) (hb : b+1≤(ball D V u (k+1)).card)
    (hc : c+1≤(ball D V u k).card) (pos : 0<lo) (cost : Room q r i j a b c lo hi) :
    (ball D V u (k+3)).card≤lo := by
  classical
  let L := fun n=>(ball D V u n).erase u
  let W := L (k+3)
  have card n : (L n).card+1=(ball D V u n).card := card_erase_add_one (self_mem_ball uv)
  have cw : W.card+1=(ball D V u (k+3)).card := card _
  have ds := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+3≤k+4 by omega))
  by_contra! wide
  rcases cost W.card (mem_Icc.mpr ⟨by omega,by omega⟩) with ⟨d,dm,fit,bad⟩|⟨keep,bad⟩|⟨keep,bad⟩
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=k+3) free uv time deg (by omega)
      (mem_Icc.mp dm).1 (mem_Icc.mp dm).2 (by omega) (by omega)
    simp only [Nat.reduceAdd,Nat.add_assoc] at lim
    omega
  · have lower s (rs : s≤r) (sr : 3≤s) (rad : s≤q) (room : 2*r+s≤2*q+3) :
        score s r W.card a b c≤∑x∈W,(ball D W x s).card := by
      apply le_trans _ (prefix_sum free uv deg time rad (by omega) rs sr room second third (by omega))
      dsimp only [score]
      apply Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_right _ ?_)) (Nat.mul_le_mul_right _ ?_)) (Nat.mul_le_mul_right _ ?_)
      all_goals first | exact (show a≤(L (k+2)).card by have := card (k+2); omega)
                      | exact (show b≤(L (k+1)).card by have := card (k+1); omega)
                      | exact (show c≤(L k).card by have := card k; omega)
    have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
    have cap := weighted_rows ff radii (score:=fun x=>(ball D W x i).card+(ball D W x j).card) (fun _ _=>le_rfl)
    rw [sum_add_distrib] at cap
    exact bad.not_ge ((Nat.add_le_add (lower i ir si (by omega) ri) (lower j jr sj (by omega) rj)).trans cap)
  · let row := fun x=>(ball D W x i).card+(ball D W x j).card
    let C := L k
    have cw' : C⊆W := erase_subset_erase u (ball_mono_radius (by omega : k≤k+3))
    have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
    have rank := minOut_prefix_erase (d:=3) free uv time deg
      (show 3+(ball D V u (k+4)\ball D V u (k+3)).card≤r by omega)
    have low x (xm : x∈W) : 3*(i+j)+2≤row x := by
      have l := ball_of_min (BRq3.ball_all (i+1) (by omega)) (ff.mono_bound (by omega)) rank x xm
      have h := ball_of_min (BRq3.ball_all (j+1) (by omega)) (ff.mono_bound (by omega)) rank x xm
      simp only [Nat.add_sub_cancel] at l h
      dsimp only [row]
      omega
    have high x (xm : x∈C) : 3*(i+j)+2+(6*r-3*(i+j))≤row x := by
      have n := third x (ball_subset (mem_of_mem_erase xm))
      have z := RetainedRadiusLayers.two_scores free uv xm (by omega : k+3≤k+3) (by omega) si sj
      change 2*(ball D V x 3).card≤row x at z
      omega
    have charge := increments (f:=row) (j:=0) (k:=0) cw' (Subset.rfl : C⊆C) (Subset.rfl : C⊆C)
      low high (by simpa only [Nat.add_zero] using high) (by simpa only [Nat.add_zero] using high)
    have upper := weighted_rows ff radii (score:=row) (fun _ _=>le_rfl)
    have better := Nat.mul_le_mul_right (6*r-3*(i+j)) (show c≤C.card by have := card k; change c≤(L k).card; omega)
    simp only [Nat.mul_zero,Nat.add_zero] at charge
    omega

attribute [aesop safe forward (immediate := [free,uv,deg,time,radii,ir,jr,si,sj,ri,rj,second,third,tiny,ha,hb,hc,pos,cost]) (rule_sets := [CHGraphFamilies])] squeeze
#print axioms squeeze
end LeanCH.BR.MixedRadiusPrefix
