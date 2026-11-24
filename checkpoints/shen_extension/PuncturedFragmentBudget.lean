import checkpoints.shen_extension.FragmentScoreEquality

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen ParentBankPeel BypassRepair

/-- The ordinary floor can be weakened to just below a marked row's
degree, to make equality force separation of the two sets. -/
def ordinaryFloor (q d k r : ℕ) := min (floorTable q d k) (r-1)

def FragmentTest (q r b h a k d : ℕ) : Prop :=
  2≤k ∧ k+k≤q ∧ 0<d ∧ d+(h-b)≤r ∧ r+(k-1)≤q*d+1 ∧
  a<b-1 ∧ b-1-a≤q*d ∧
  (b-1)*b≤2*(a*(r+(k-1)+1)+(b-1-a)*(ordinaryFloor q d k r+1))

instance (q r b h a k d : ℕ) : Decidable (FragmentTest q r b h a k d) := by
  unfold FragmentTest; infer_instance

/-- On an arbitrary punctured prefix, the preceding punctured ball
keeps all its rows. The shell after the prefix pays for the minimum
degree lost by the remaining rows. All radii and counts are free. -/
theorem prefix_exclusion {D V q r u i k d} (free : QFree D V q) (uv : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (time : i+2≤q)
    (known : ∀t,t≤d → NoHost q t) :
    ¬FragmentTest q r (ball D V u (i+1)).card (ball D V u (i+2)).card
      ((ball D V u i).erase u).card k d := by
  intro cfg
  obtain ⟨depth,radii,pos,loss,seed,live,size,cost⟩ := cfg
  let W := (ball D V u (i+1)).erase u
  let H := (ball D V u i).erase u
  have sub : H⊆W := erase_subset_erase _ (ball_mono_radius (Nat.le_succ i))
  have wv : W⊆V := (erase_subset u _).trans ball_subset
  have wf := free.mono_set wv
  have ws : W.card=(ball D V u (i+1)).card-1 := card_erase_of_mem (self_mem_ball uv)
  have wb : W.card+1=(ball D V u (i+1)).card := card_erase_add_one (self_mem_ball uv)
  have rootpos : 0<r := by omega
  have floor : ∀x∈W,d≤(outN D W x).card := by
    apply minOut_prefix_erase free uv time degree
    rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _))]
    exact loss
  have full x (xm : x∈H) : r≤(outN D W x).card := by
    have hv := mem_of_mem_erase xm
    exact (degree x (ball_subset hv)).trans (card_le_card (outN_prefix_erase_root free uv
      (show i+1≤q by omega) hv))
  let lo := ordinaryFloor q d k r
  have ordinary x (xm : x∈W) : lo+1≤(ball D W x k).card :=
    (Nat.add_le_add_right (Nat.min_le_left _ _) 1).trans
      (floor_table wf floor (fun t l=>known t l.le) (by omega) pos xm k (by omega))
  have marked x (xm : x∈H) : r+(k-1)+1≤(ball D W x k).card := by
    have step := grow_seed (k:=k-1) (j:=k-1) wf (sub xm) floor (full x xm)
      rootpos (known d le_rfl) (by omega) seed le_rfl
    rwa [Nat.sub_add_cancel (by omega : 1≤k)] at step
  have low : lo<r := lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
  have cap := strict_fragment_budget wf radii depth sub floor full ordinary marked low
    (show H.card<W.card by rw [ws]; exact live)
    (show W.card-H.card≤q*d by rw [ws]; exact size) (known d le_rfl)
  change (ball D V u (i+1)).card-1 > H.card at live
  change ((ball D V u (i+1)).card-1)*(ball D V u (i+1)).card ≤
    2*(H.card*(r+(k-1)+1)+((ball D V u (i+1)).card-1-H.card)*(lo+1)) at cost
  rw [←ws,←wb] at cost
  omega

#print axioms prefix_exclusion
end LeanCH.BR.FragmentScoreEquality