import checkpoints.shen_extension.NearTotalTensor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace LeanCH.BR.ShenShellTraffic
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- The two contractions count the same labelled (root,marked vertex)
incidences of an exact distance layer. -/
theorem transpose_between (D : CH.Digraph) (V X : Finset ℕ) (k l : ℕ) :
    (∑ u∈V, (X.filter (fun x => x∈ball D V u l ∧ x∉ball D V u k)).card) =
      ∑ x∈X, (reverseBall D V x l \ reverseBall D V x k).card := by
  have col (x) : reverseBall D V x l \ reverseBall D V x k =
      V.filter (fun u => x∈ball D V u l ∧ x∉ball D V u k) := by
    ext u
    simp only [reverseBall,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  simp only [col,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- Bound the total exposure of an arbitrary exceptional set to all
forward layers. A discrepancy of the preceding reverse ball is paid
once per marked vertex, and its total follows from a forward floor. -/
theorem exposure_between {D : CH.Digraph} {V X : Finset ℕ} {k l L J K : ℕ} (radii : k≤l)
    (sub : X⊆V) (order : L≤J) (mono : J≤K)
    (low : ∀ x∈V, L≤(ball D V x k).card)
    (upper : ∀ x∈V, (reverseBall D V x k).card≤J)
    (outer : ∀ x∈V, (reverseBall D V x l).card≤K) :
    (∑ u∈V, (X.filter (fun x => x∈ball D V u l ∧ x∉ball D V u k)).card) ≤
      X.card*(K-J)+V.card*(J-L) := by
  rw [transpose_between]
  let deficit := fun x => J-(reverseBall D V x k).card
  have localBound (x) (hx : x∈X) :
      (reverseBall D V x l \ reverseBall D V x k).card≤(K-J)+deficit x := by
    have inc : reverseBall D V x k ⊆ reverseBall D V x l := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
        ball_mono_radius radii (Finset.mem_filter.mp hu).2⟩
    have := Finset.card_sdiff_add_card_eq_card inc
    have := outer x (sub hx)
    have := upper x (sub hx)
    dsimp [deficit]; omega
  have one (x) (hx : x∈V) : deficit x+(reverseBall D V x k).card=J := by
    dsimp [deficit]; have := upper x hx; omega
  have eq := Finset.sum_congr (s₁:=V) rfl one
  rw [Finset.sum_add_distrib,sum_reverseBall_eq_sum_ball,Finset.sum_const_nat (fun _ _ => rfl)] at eq
  have lb := Finset.sum_le_sum low
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lb
  have id := congrArg (fun n : ℕ => V.card*n) (show J-L+L=J by omega)
  rw [Nat.mul_add] at id
  have markedSum := Finset.sum_le_sum_of_subset_of_nonneg (f:=deficit) sub (fun _ _ _ => Nat.zero_le _)
  have total := Finset.sum_le_sum localBound
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at total
  omega

theorem transpose (D : CH.Digraph) (V X : Finset ℕ) (k : ℕ) :
    (∑ u∈V, (X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)).card) =
      ∑ x∈X, (reverseBall D V x (k+1) \ reverseBall D V x k).card  := transpose_between D V X k (k+1)

theorem exposure {D : CH.Digraph} {V X : Finset ℕ} {k L J K : ℕ}
    (sub : X⊆V) (order : L≤J) (mono : J≤K)
    (low : ∀ x∈V, L≤(ball D V x k).card)
    (upper : ∀ x∈V, (reverseBall D V x k).card≤J)
    (outer : ∀ x∈V, (reverseBall D V x (k+1)).card≤K) :
    (∑ u∈V, (X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)).card) ≤
      X.card*(K-J)+V.card*(J-L) :=
  exposure_between (by omega) sub order mono low upper outer

#print axioms transpose
#print axioms exposure

/-- Select a root from any specified eligible family. Both the extra
cost of the chosen root and the bad vertices in its *own* layer are small. -/
theorem select_root {D : CH.Digraph} {V X Z : Finset ℕ} {k L J K E T : ℕ}
    (sub : X⊆V) (zsub : Z⊆V) (ne : Z.Nonempty) (order : L≤J) (mono : J≤K)
    (low : ∀ x∈V, L≤(ball D V x k).card)
    (upper : ∀ x∈V, (reverseBall D V x k).card≤J)
    (outer : ∀ x∈V, (reverseBall D V x (k+1)).card≤K)
    (cost : ℕ → ℕ) (hc : (∑ u∈Z,cost u)≤E)
    (room : E+X.card*(K-J)+V.card*(J-L)≤Z.card*T) :
    ∃ u∈Z, cost u+(X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)).card≤T := by
  let hit := fun u => (X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)).card
  by_contra! bad
  have ex := exposure sub order mono low upper outer
  have eligibleSum := Finset.sum_le_sum_of_subset_of_nonneg (f:=hit) zsub (fun _ _ _ => Nat.zero_le _)
  change (∑ u∈V,hit u)≤_ at ex
  have high := Finset.sum_le_sum (fun u hu => (show T+1≤cost u+hit u from bad u hu))
  rw [Finset.sum_const_nat (fun _ _ => rfl),Finset.sum_add_distrib,Nat.mul_add,Nat.mul_one] at high
  have := Finset.card_pos.mpr ne
  omega

#print axioms select_root

/-- At a selected almost-flat even-cutoff root, the exceptional vertices
and row holes cannot account for all of the nearly coincident reach rows. -/
theorem selected_table_false {D : CH.Digraph} {V S T X : Finset ℕ} {s r b : ℕ}
    (scale : 8192≤s) (radius : r+5=s) (hf : QFree D V (2*(r+1)))
    (hSV : S⊆V) (hTV : T⊆V)
    (wide : s≤S.card+2) (heads : 7*s≤8*(T.card+1)) (badCount : 8*(S∩X).card≤s)
    (holes : (∑ x∈S,(T \ outN D T x).card)≤2*s)
    (low : ∀ y∈T, b+1≤(ball D V y r).card+s)
    (upper : ∀ x∈S \ X, (ball D V x (r+1)).card≤b+63)
    (missing : ∀ x∈S \ X,
      (V.filter (fun y => y∉ball D V x (r+1) ∧ x∉ball D V y (r+1))).card≤63) : False := by
  let miss := fun x => (T \ outN D T x).card
  let W := S \ X
  let A := W.filter (fun x => miss x≤8)
  let e := (9*s)/16+71
  have sub : A⊆W := Finset.filter_subset _ _
  have subW : W⊆S := Finset.sdiff_subset
  have splitS : W.card+(S∩X).card=S.card := Finset.card_sdiff_add_card_inter _ _
  have splitW := Finset.card_sdiff_add_card_eq_card sub
  have high (x) (hx : x∈W \ A) : 9≤miss x := by
    obtain ⟨hxW,hno⟩ := Finset.mem_sdiff.mp hx
    by_contra! lo
    exact hno (Finset.mem_filter.mpr ⟨hxW,by omega⟩)
  have discarded := Finset.sum_le_sum high
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at discarded
  have hh := (Finset.sum_le_sum_of_subset_of_nonneg (f:=miss)
    ((Finset.sdiff_subset (s:=W) (t:=A)).trans subW) (fun _ _ _ => Nat.zero_le _))
  have hd : (W \ A).card*9≤2*s := discarded.trans (hh.trans holes)
  have size : 47*s≤72*A.card+144 := by omega
  have ne := Finset.card_pos.mp (show 0<A.card by omega)
  have close (x) (hx : x∈A) (y) (hy : y∈A) :
      (ball D V x (r+1) \ ball D V y (r+1)).card≤e := by
    apply ShenCommonSuccessor.pair_row_diff (b:=b+1-s) (N:=b+63) (g:=8) hf hTV (by omega)
      (fun z hz => by have := low z hz; omega) (upper x (sub hx))
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (by omega) _
    dsimp [e]; omega
  have bound := ShenNearTotal.row_capacity (d:=63) hf (sub.trans (subW.trans hSV)) ne
    (by dsimp [e]; omega) (by dsimp [e]; omega) close (by
      intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (sub.trans (subW.trans hSV)))).trans
        (missing x (sub hx)))
  dsimp [e] at bound
  omega

#print axioms selected_table_false

private theorem tail_count (V : Finset ℕ) (f : ℕ → ℕ) (t : ℕ) :
    (V.filter (fun x => t≤f x)).card*t≤∑ x∈V,f x := by
  let X := V.filter (fun x => t≤f x)
  have bound (x) (hx : x∈X) : t≤f x := (Finset.mem_filter.mp hx).2
  have h := Finset.sum_le_sum bound
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h
  exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _))

/-- The even top-order packet from the local next-depth paper suffices
for contradiction. The assumptions are forward ball floors and the
boundary width and hole bound at all minimum middle-ball roots. -/
theorem even_packet_false {D : CH.Digraph} {V : Finset ℕ} {s k b : ℕ}
    (scale : 8192≤s) (radius : k+6=s) (roomB : 2*s≤b)
    (hf : QFree D V (2*(k+2))) (ne : V.Nonempty) (ord : V.card≤2*b)
    (floor0 : ∀ x∈V, b-2*s+1≤(ball D V x k).card)
    (floor1 : ∀ x∈V, b-s+1≤(ball D V x (k+1)).card)
    (floor2 : ∀ x∈V, b≤(ball D V x (k+2)).card)
    (floor3 : ∀ x∈V, b+s-1≤(ball D V x (k+3)).card)
    (floor4 : ∀ x∈V, b+2*s-5≤(ball D V x (k+4)).card)
    (wide : ∀ u∈V, (ball D V u (k+2)).card=b →
      s≤(ball D V u (k+1) \ ball D V u k).card+2)
    (holes : ∀ u∈V, (ball D V u (k+2)).card=b →
      (∑ x∈ball D V u (k+1) \ ball D V u k,
        ((ball D V u (k+2) \ ball D V u (k+1)) \ outN D (ball D V u (k+2) \ ball D V u (k+1)) x).card)≤2*s) :
    False := by
  let e := fun x => (ball D V x (k+2)).card-b
  let a := fun x => (ball D V x (k+1)).card-(b-s+1)
  let d := fun x => (V.filter (fun y => y∉ball D V x (k+2) ∧ x∉ball D V y (k+2))).card
  let X := V.filter (fun x => 64≤e x+d x)
  let Z := V.filter (fun x => e x=0)
  have hZ : Z⊆V := Finset.filter_subset _ _
  have counts {i v : ℕ} (f : ∀ x∈V,v≤(ball D V x i).card) :
      (∑ x∈V,((ball D V x i).card-v))+V.card*v=∑ x∈V,(ball D V x i).card := by
    have he := Finset.sum_congr (s₁:=V) rfl (fun x hx => Nat.sub_add_cancel (f x hx))
    rwa [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at he
  have ec := counts floor2
  change (∑ x∈V,e x)+V.card*b=_ at ec
  have ac := counts floor1
  change (∑ x∈V,a x)+V.card*(b-s+1)=_ at ac
  have gb := ShenNearTotal.pair_budget (l:=k+2) hf (by omega : (k+2)+(k+2)≤2*(k+2)) le_rfl le_rfl
  have dc : (ShenNearTotal.incomparablePairs D V V (k+2)).card= ∑ x∈V,d x := by
    simp only [ShenNearTotal.incomparablePairs,d,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_product V V _
  rw [dc] at gb
  have ar : V.card*(V.card+1)≤2*(V.card*b)+V.card := by
    nlinarith only [Nat.mul_le_mul_left V.card ord]
  have both : (∑ x∈V,d x)+2*(∑ x∈V,e x)≤V.card := by omega
  have bad := tail_count V (fun x => e x+d x) 64
  change X.card*64≤_ at bad
  rw [Finset.sum_add_distrib] at bad
  have m : X.card*64≤V.card := by omega
  have lc := tail_count V e 1
  have missingMin : V.filter (fun x => 1≤e x)=V \ Z := by
    ext x
    simp only [Z,Finset.mem_sdiff,Finset.mem_filter]
    by_cases hx : x∈V <;> simp [hx] <;> omega
  rw [missingMin,Nat.mul_one] at lc
  have sc := Finset.card_sdiff_add_card_eq_card hZ
  have zLarge : V.card≤2*Z.card := by omega
  have zne := Finset.card_pos.mp (show 0<Z.card by have := Finset.card_pos.mpr ne; omega)
  have ca := tensor_capacity_identity hf (by omega : (k+1)+(k+3)≤2*(k+2))
  have lb := Finset.sum_le_sum floor3
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lb
  have prod := congrArg (fun n : ℕ => V.card*n) (show (b-s+1)+(b+s-1)=2*b by omega)
  rw [Nat.mul_add] at prod
  have sa : (∑ u∈Z,a u)≤V.card := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f:=a) hZ (fun _ _ _ => Nat.zero_le _)
    nlinarith only [this,ac,ca,lb,prod,ar,Nat.zero_le (∑ u∈V,
      (V \ (ball D V u (k+1) ∪ reverseBall D V u (k+3))).card)]
  have rev0 (u) (hu : u∈V) : (reverseBall D V u k).card≤b-2*s+6 := by
    have := reverseBall_add_ball_le (v:=u) hf (by omega : (k+4)+k≤2*(k+2))
    have := floor4 u hu; omega
  have rev1 (u) (hu : u∈V) : (reverseBall D V u (k+1)).card≤b-s+2 := by
    have := reverseBall_add_ball_le (v:=u) hf (by omega : (k+3)+(k+1)≤2*(k+2))
    have := floor3 u hu; omega
  have afford : V.card+X.card*((b-s+2)-(b-2*s+6))+V.card*((b-2*s+6)-(b-2*s+1))
      ≤Z.card*(s/8) := by
    rw [show (b-2*s+6)-(b-2*s+1)=5 by omega]
    have h1 := Nat.mul_le_mul_left X.card (show (b-s+2)-(b-2*s+6)≤s by omega)
    have h2 := Nat.mul_le_mul_right s m
    have h3 := Nat.mul_le_mul_right (s/8) zLarge
    have h4 := Nat.mul_le_mul_left V.card (show 384+s≤32*(s/8) by omega)
    nlinarith only [h1,h2,h3,h4]
  obtain ⟨u,uz,sel⟩ := select_root (show X⊆V from Finset.filter_subset _ _) hZ zne
    (by omega) (by omega) floor0 rev0 rev1 a sa afford
  have uv := hZ uz
  have mid : (ball D V u (k+2)).card=b := by
    have h := (Finset.mem_filter.mp uz).2; change e u=0 at h
    dsimp [e] at h; have := floor2 u uv; omega
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  have Ssub : S⊆V := Finset.sdiff_subset.trans ball_subset
  have eqX : X.filter (fun x => x∈ball D V u (k+1) ∧ x∉ball D V u k)=S∩X := by
    ext x; simp [S]; tauto
  rw [eqX] at sel
  have tc : T.card+(ball D V u (k+1)).card=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have au : a u+(b-s+1)=(ball D V u (k+1)).card := Nat.sub_add_cancel (floor1 u uv)
  have good (x) (hx : x∈S \ X) : e x+d x≤63 := by
    obtain ⟨hxS,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! large
    exact hn (Finset.mem_filter.mpr ⟨Ssub hxS,by omega⟩)
  apply selected_table_false (r:=k+1) (b:=b) (X:=X) scale (by omega) hf Ssub
    (show T⊆V from Finset.sdiff_subset.trans ball_subset) (wide u uv mid) (by omega) (by omega) (holes u uv mid)
  · intro y hy; have := floor1 y (ball_subset (Finset.mem_sdiff.mp hy).1); omega
  · intro x hx
    have h := good x hx
    change (ball D V x (k+2)).card≤b+63
    dsimp only [e] at h; omega
  · intro x hx; have := good x hx; change d x≤63; omega

#print axioms even_packet_false
end LeanCH.BR.ShenShellTraffic
