import checkpoints.shen_extension.PrimaryContactClosure

namespace LeanCH.BR.LowShellCycleSelection
open Finset CHRuleCatalog

/-- Try every attainable score up to the order and retain the largest
certified one. The checker below revalidates the selected floors. -/
def bestFloor (n : ℕ) (rule : ℕ → Bool) :=
  (List.range (n+1)).foldl (fun best i => if rule i then i else best) 0

def proposedFloors (n r q : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let g := bestFloor n (fun i => decide (ScoreRoom q r (r-1) i))
  let mid := bestFloor n (fun i => decide (GrowthRoom q r g i))
  let top := bestFloor n (fun i => decide (GrowthRoom q r mid i))
  let cap := ((n-((r-1)+top))*2) / fullRowFloor q r
  (g,mid,top,cap)

private def routeTest (n r q g : ℕ) : Prop :=
  Room q r ∧ ShellBankOrders.MixedRoom q r ∧ n≤2*(3*r) ∧ r≤q+2 ∧ r+1<2*(q-1) ∧
  (r-(q+1))*(r-q)+3≤q ∧ ScoreRoom q r (r-1) g ∧ 3*r<4+g ∧
  CompressionRoom q r (r-1) (2*(r-1)+1) (3*(r-1)) ∧
  n<(q+1)*(r-1) ∧ 2*(r-q+1)<3*((q+1)-(r-(q+1))*(r-q))

private instance {n r q g} : Decidable (routeTest n r q g) := by unfold routeTest; infer_instance

def floorTest (n r q g mid top cap : ℕ) : Prop :=
  routeTest n r q g ∧ TransferRoom q r n g mid top ∧
  (n-((r-1)+top))*2<(cap+1)*fullRowFloor q r ∧ cap+1<3*(r-1) ∧
  cap+5<3*(r-1) ∧ 4*(r-q+1)<3*fullRowFloor q r ∧ CompletePriceRoom q r ∧
  ArrivalRoom q r (n-((r-1)+top)) cap ∧ n+8<(r-1)+top+3*(r-1) ∧
  (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14

instance {n r q g mid top cap} : Decidable (floorTest n r q g mid top cap) := by unfold floorTest; infer_instance

def searchedWindow (n r q : ℕ) : Prop :=
  let (g,mid,top,cap) := proposedFloors n r q
  floorTest n r q g mid top cap

instance {n r q} : Decidable (searchedWindow n r q) := by unfold searchedWindow; dsimp; infer_instance

theorem window_of_search {n r q} (hit : searchedWindow n r q) : PrimaryContactWindow n r q := by
  unfold searchedWindow at hit
  generalize proposedFloors n r q=cert at hit
  obtain ⟨g,mid,top,cap⟩ := cert
  obtain ⟨route,transfer,crowd,spare,rest⟩ := hit
  obtain ⟨cycle,growth,small,close,space,dist,score,high,squeeze,finite,margin⟩ := route
  exact ⟨g,g,mid,top,cap,⟨⟨cycle,growth,small,close,space,dist,score,high,squeeze,finite,margin⟩,
    transfer,crowd,spare⟩,rest⟩

theorem outside_search {p : Input} (bad : Bad p) : ¬searchedWindow p.n p.s (cutoff p) :=
  fun hit=>outside_primary_contact_window bad (window_of_search hit)

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] outside_search
#print axioms window_of_search
#print axioms outside_search
end LeanCH.BR.LowShellCycleSelection
