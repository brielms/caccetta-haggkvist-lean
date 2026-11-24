import checkpoints.shen_extension.MixedRadiusPrefix
import checkpoints.shen_extension.OddBoundaryLayers
namespace LeanCH.BR.OddShellOrder
open Finset BRq2 BRq3 BR45 BRsGen MixedRadiusPrefix

def Capacity (q r i j : ℕ) : Prop :=
  7≤r ∧ r+1≤q ∧ 9≤q ∧ 3≤ i ∧ 3≤j ∧ i≤r ∧ j≤r ∧ i+j≤q ∧
  2*r+i≤2*q+3 ∧ 2*r+j≤2*q+3 ∧
  Room q r i j (2*r) r 0 (3*r+1) (4*r-1) ∧
  Room q r i j (3*r) (2*r) r (4*r) (5*r-2) ∧
  Room q r i j (2*r) r 0 (3*r+2) (4*r)
instance (q r i j) : Decidable (Capacity q r i j) := by unfold Capacity; infer_instance

/-- An odd cutoff spends different radii on the forward and reverse
balls. At equality the third layer of a physical root transfers into the
second layer of its own sink, exceeding that sink's derived capacity. -/
theorem order {D V q r i j} (free : QFree D V q) (live : V.Nonempty)
    (degree : ∀v∈V,r≤(outN D V v).card) (room : Capacity q r i j) : 9*r+1≤V.card := by
  obtain ⟨hr,time,nine,si,sj,ir,jr,radii,ri,rj,guard4,guard5,guard3⟩ := room
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have deg x (xm : x∈V) := (reg x xm).ge
  have sec x (xm : x∈V) := card_ball_two_ge_twice (by omega : 2≤r) (ff.mono_bound (by omega)) deg xm
  have third x (xm : x∈V) : 3*r+1≤(ball F V x 3).card := by
    by_contra! less
    exact (Nat.ne_of_lt less) (BoundaryPrefixRank.third_tight ff xm deg (by omega) time less.le).2
  have first x (xm : x∈V) : (ball F V x 1).card=r+1 := by
    rw [card_B1 (ff.mono_bound (by omega : 4≤q)) xm,reg x xm]
  have zero x (xm : x∈V) : (ball F V x 0).card=1 := by
    have eq : ball F V x 0={x} := eq_of_subset_of_card_le
      (fun _ m=>mem_singleton.mpr (eq_of_mem_ball_zero m)) (by
        rw [card_singleton]; exact card_pos.mpr ⟨x,self_mem_ball xm⟩)
    rw [eq,card_singleton]
  have bound u (um : u∈V) {lo hi : ℕ} (tiny : (ball F V u 4).card≤hi+1)
      (pos : 0<lo) (cost : Room q r i j (2*r) r 0 lo hi) : (ball F V u 3).card≤lo :=
    MixedRadiusPrefix.squeeze (k:=0) ff um deg (by omega) radii ir jr si sj ri rj sec third tiny
      (sec u um) (first u um).ge (zero u um).ge pos cost
  have fourth u (um : u∈V) : 4*r+1≤(ball F V u 4).card := by
    by_contra! small
    have cap := bound u um (show (ball F V u 4).card≤4*r-1+1 by omega) (by omega) guard4
    obtain ⟨two,three⟩ := BoundaryPrefixRank.third_tight ff um deg (by omega) time cap
    have a := zero u um
    have b := first u um
    have dif (k : ℕ) := card_sdiff_add_card_eq_card (ball_mono_radius (D:=F) (W:=V) (u:=u) (show k≤k+1 by omega))
    have layers k (hk : k<3) : (ball F V u (k+1)\ball F V u k).card=r := by
      have := dif k
      interval_cases k <;> simp only [Nat.reduceAdd] at * <;> omega
    have inc := EqualLayerTransit.next_layer ff um deg (by omega) (by omega) (by omega : r/2+3≤q) (by decide) layers
    have sum := dif 3
    simp only [Nat.reduceAdd] at inc sum
    omega
  have fifth u (um : u∈V) : 5*r≤(ball F V u 5).card := by
    by_contra! small
    have cap := MixedRadiusPrefix.squeeze (k:=1) ff um deg (by omega) radii ir jr si sj ri rj sec third
      (show (ball F V u 5).card≤5*r-2+1 by omega) (third u um) (sec u um) (first u um).ge (by omega) guard5
    have := fourth u um
    change (ball F V u 4).card≤4*r at cap
    omega
  have orderSize := card_ge_of_two_balls ff (by omega : 4+5≤q) fourth fifth live
  by_contra! small
  have exactSizes := two_balls_boundary_cards ff (by omega : 4+5≤q) fourth fifth (by omega)
  apply OddBoundaryLayers.exclude_flat ff live reg hr time _ (fun u um=>(exactSizes u um).1) (fun u um=>(exactSizes u um).2.1)
  intro u um
  exact bound u um (exactSizes u um).1.le (by omega) guard3

attribute [aesop safe forward (immediate := [free,live,degree,room]) (rule_sets := [CHGraphFamilies])] order
#print axioms order
end LeanCH.BR.OddShellOrder
