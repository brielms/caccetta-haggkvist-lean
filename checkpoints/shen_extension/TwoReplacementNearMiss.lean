import checkpoints.shen_extension.TwoReplacementContraction

/-! A pair of rows supplies the two additional heads when the common bank is one short. -/
namespace LeanCH.BR.Closure.TwoReplacement.NearMiss
open Finset BRq2 BRq3

/-- A row assigned as a singly credited parent must use the opposite copy as its head. -/
def signature (D : CH.Digraph) (R : Finset ℕ) (x : ℕ) : Finset ℕ :=
  outN D R x ∪ (if x ∈ R then {x} else ∅)

def share (R T : Finset ℕ) (x : ℕ) : ℕ :=
  (if x ∈ R then 1 else 0) + (if x ∈ T then 2 else 0)

def commonBank (D : CH.Digraph) (W R T : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (W \ (T ∪ R)).filter (fun x => d ≤ (outN D (W \ (T ∪ R)) x).card)

/-- Partition R so that the two rows spend at most a and b on conflicting requirements. -/
theorem split_pair {L M R : Finset ℕ} (lr : L ⊆ R) (mr : M ⊆ R) (a b : ℕ) :
    (∃ K ⊆ R, (L ∩ K).card ≤ a ∧ (M ∩ (R \ K)).card ≤ b) ↔ (L ∩ M).card ≤ a+b := by
  constructor
  · rintro ⟨K,_,lc,mc⟩
    have bound := card_union_le (L ∩ K) (M ∩ (R \ K))
    have incl : L ∩ M ⊆ (L ∩ K) ∪ (M ∩ (R \ K)) := by
      intro x hx
      obtain ⟨xl,xm⟩ := mem_inter.mp hx
      by_cases xk : x ∈ K
      · exact mem_union_left _ (mem_inter.mpr ⟨xl,xk⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨xm,mem_sdiff.mpr ⟨mr xm,xk⟩⟩)
    have := card_le_card incl
    omega
  · intro bound
    let I := L ∩ M
    obtain ⟨H,hi,count⟩ := exists_subset_card_eq (min_le_right a I.card)
    let K := (M \ L) ∪ H
    have kr : K ⊆ R := union_subset (sdiff_subset.trans mr) (hi.trans (inter_subset_left.trans lr))
    have left : L ∩ K = H := by
      ext x
      have carry (h : x ∈ H) : x ∈ L := (mem_inter.mp (hi h)).1
      simp only [K,mem_inter,mem_union,mem_sdiff]
      tauto
    have right : M ∩ (R \ K) = I \ H := by
      ext x
      have carry (h : x ∈ M) := mr h
      simp only [I,K,mem_inter,mem_union,mem_sdiff]
      tauto
    refine ⟨K,kr,?_,?_⟩
    · rw [left,count]; exact min_le_left _ _
    · rw [right,card_sdiff_of_subset hi,count]
      change I.card ≤ a+b at bound
      omega

private theorem signature_sub (D : CH.Digraph) (R) (x) : signature D R x ⊆ R := by
  by_cases h : x ∈ R
  · simpa [signature,h] using (union_subset (outN_subset (D:=D) (W:=R) (y:=x)) (singleton_subset_iff.mpr h))
  · simpa [signature,h] using (outN_subset (D:=D) (W:=R) (y:=x))

private theorem one_head {D : CH.Digraph} {W R T K P Q : Finset ℕ} {d x a : ℕ}
    (rw' : R ⊆ W) (tw : T ⊆ W) (kr : K ⊆ R)
    (xw : x ∈ W) (xt : x ∉ T) (hard : x ∈ R → a=0)
    (allowance : d + (outN D T x).card + a ≤ (outN D W x).card + credit P Q x)
    (few : (signature D R x ∩ K).card ≤ a) :
    x ∈ pool D W P Q (T ∪ K) d := by
  have outside : x ∉ K := by
    intro xk
    have xr := kr xk
    have mem : x ∈ signature D R x ∩ K :=
      mem_inter.mpr ⟨mem_union_right _ (by simp [xr]),xk⟩
    have pos := card_pos.mpr ⟨_,mem⟩
    have := hard xr
    omega
  have bank := union_subset tw (kr.trans rw')
  have lost : (outN D (T ∪ K) x).card ≤ (outN D T x).card + a := by
    have sub : outN D (T ∪ K) x ⊆ outN D T x ∪ (signature D R x ∩ K) := by
      intro y hit
      obtain ⟨h,edge⟩ := mem_outN.mp hit
      rcases mem_union.mp h with yt | yk
      · exact mem_union_left _ (mem_outN.mpr ⟨yt,edge⟩)
      · exact mem_union_right _ (mem_inter.mpr
          ⟨mem_union_left _ (mem_outN.mpr ⟨kr yk,edge⟩),yk⟩)
    have := card_le_card sub
    have := card_union_le (outN D T x) (signature D R x ∩ K)
    omega
  have eq : outN D (W \ (T ∪ K)) x = outN D W x \ outN D (T ∪ K) x := by
    ext y; simp only [mem_outN,mem_sdiff]; tauto
  have sub : outN D (T ∪ K) x ⊆ outN D W x := fun y h =>
    mem_outN.mpr ⟨bank (mem_outN.mp h).1,(mem_outN.mp h).2⟩
  apply mem_filter.mpr
  refine ⟨mem_sdiff.mpr ⟨xw,fun h => (mem_union.mp h).elim xt outside⟩,?_⟩
  rw [eq,card_sdiff_of_subset sub]
  omega

/-- Sets R and T receive one and two credits. At a four-label deletion these are
the rows losing two and three heads. The result produces the actual split K. -/
theorem pair_feasible {D : CH.Digraph} {W R T : Finset ℕ} {d x z a b : ℕ}
    (rw' : R ⊆ W) (tw : T ⊆ W) (rt : Disjoint R T)
    (base : ∀ y ∈ W, d ≤ (outN D W y).card + share R T y)
    (near : d ≤ (commonBank D W R T d).card + 1)
    (xw : x ∈ W) (zw : z ∈ W) (xz : x ≠ z) (xt : x ∉ T) (zt : z ∉ T)
    (xb : x ∉ commonBank D W R T d) (zb : z ∉ commonBank D W R T d)
    (hx : x ∈ R → a=0) (hz : z ∈ R → b=0)
    (ax : d + (outN D T x).card + a ≤ (outN D W x).card + share R T x)
    (az : d + (outN D T z).card + b ≤ (outN D W z).card + share R T z)
    (overlap : (signature D R x ∩ signature D R z).card ≤ a+b) :
    ∃ K ⊆ R, Feasible D W (T ∪ K) (T ∪ (R \ K)) d := by
  obtain ⟨K,kr,left,right⟩ := (split_pair (signature_sub D R x) (signature_sub D R z) a b).mpr overlap
  let P := T ∪ K
  let Q := T ∪ (R \ K)
  let B := commonBank D W R T d
  have un : P ∪ Q = T ∪ R := by
    ext y
    have incl (h : y ∈ K) := kr h
    simp only [P,Q,mem_union,mem_sdiff]
    tauto
  have credits (y : ℕ) : credit P Q y = share R T y := by
    by_cases yt : y ∈ T
    · have yr : y ∉ R := fun h => disjoint_left.mp rt h yt
      simp [credit,share,P,Q,yt,yr]
    · by_cases yk : y ∈ K
      · simp [credit,share,P,Q,yt,yk,kr yk]
      · by_cases yr : y ∈ R <;> simp [credit,share,P,Q,yt,yk,yr]
  have cx : x ∈ pool D W P Q P d :=
    one_head rw' tw kr xw xt hx (by rw [credits]; exact ax) left
  have cz : z ∈ pool D W P Q Q d :=
    one_head rw' tw sdiff_subset zw zt hz (by rw [credits]; exact az) right
  have both : B ⊆ pool D W P Q (P ∪ Q) d := by
    intro y h
    obtain ⟨outside,deg⟩ := mem_filter.mp h
    apply mem_filter.mpr
    rw [un]
    exact ⟨outside,by omega⟩
  let A0 := pool D W P Q P d
  let A1 := pool D W P Q Q d
  have leftBank : insert x B ⊆ A0 := insert_subset cx (both.trans (pool_anti subset_union_left))
  have rightBank : insert z B ⊆ A1 := insert_subset cz (both.trans (pool_anti subset_union_right))
  have sizeX : d ≤ (insert x B).card := by rw [card_insert_of_notMem xb]; exact near
  have sizeZ : d ≤ (insert z B).card := by rw [card_insert_of_notMem zb]; exact near
  have inter : insert x B ∩ insert z B ⊆ pool D W P Q (P ∪ Q) d := by
    intro y h
    apply both
    simp only [mem_inter,mem_insert] at h
    grind
  refine ⟨K,kr,fun y yw => (credits y).symm ▸ base y yw,?_⟩
  exact (assign_heads (pool_anti subset_union_left) (pool_anti subset_union_right)).mp
    ⟨insert x B,leftBank,insert z B,rightBank,sizeX,sizeZ,inter⟩

/-- A sink among the singly funded parents forces two distinct usable extra heads.
The proof uses triangle-freeness on the surviving labels. -/
theorem sink_feasible {D : CH.Digraph} {W R : Finset ℕ} {d r : ℕ}
    (safe : QFree D W 3) (hd : 2 ≤ d) (rw' : R ⊆ W) (rr : r ∈ R)
    (sink : outN D R r = ∅) (rsize : (outN D W r).card + 1 = d)
    (base : ∀ y ∈ W, d ≤ (outN D W y).card + share R ∅ y)
    (near : (commonBank D W R ∅ d).card + 1 = d) :
    ∃ K ⊆ R, Feasible D W K (R \ K) d := by
  let B := commonBank D W R ∅ d
  have rW := rw' rr
  have rb : r ∉ B := by
    intro h
    exact (mem_sdiff.mp (mem_filter.mp h).1).2 (mem_union_right _ rr)
  have zExists : ∃ z ∈ W, z ≠ r ∧ z ∉ B ∧ D z r ≠ true := by
    by_contra! no
    have incoming (z) (zw : z ∈ W) (zr : z ≠ r) (zb : z ∉ B) : D z r = true := by
      simpa using no z zw zr zb
    have incl : outN D W r ⊆ B := by
      intro z h
      obtain ⟨zw,rz⟩ := mem_outN.mp h
      have zr : z ≠ r := fun e => loopfree safe (by decide) rW (e ▸ rz)
      by_contra zb
      exact digonfree safe (by decide) rW zw rz (incoming z zw zr zb)
    have bsize : B.card+1=d := near
    have rowEq : outN D W r = B := eq_of_subset_of_card_le incl (by omega)
    obtain ⟨b,bb⟩ := card_pos.mp (show 0<B.card by omega)
    have rbArc := (mem_outN.mp (rowEq.symm ▸ bb)).2
    have bw := (mem_sdiff.mp (mem_filter.mp bb).1).1
    have trapped : outN D W b ⊆ B := by
      intro z h
      obtain ⟨zw,bz⟩ := mem_outN.mp h
      by_contra zb
      by_cases eq : z=r
      · exact digonfree safe (by decide) rW bw rbArc (eq ▸ bz)
      · exact safe r 3 (by decide) (by decide)
          (.step bw rbArc (.step zw bz (.step rW (incoming z zw eq zb) (.refl r))))
    have br : b ∉ R := fun h => (mem_sdiff.mp (mem_filter.mp bb).1).2 (mem_union_right _ h)
    have deg := base b bw
    simp [share,br] at deg
    have := card_le_card trapped
    omega
  obtain ⟨z,zw,zr,zb,no⟩ := zExists
  have sigR : signature D R r = {r} := by simp [signature,rr,sink]
  have absent : r ∉ signature D R z := by
    intro h
    rcases mem_union.mp h with h|h
    · exact no (mem_outN.mp h).2
    · by_cases hz : z ∈ R
      · have eq : r=z := by simpa [hz] using h
        exact zr eq.symm
      · simp [hz] at h
  have inter : signature D R r ∩ signature D R z = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_left.mpr (by
      intro y h yz
      have yr : y = r := by simpa [sigR] using h
      exact absent (yr ▸ yz)))
  have ax (x) (xw : x ∈ W) :
      d+(outN D ∅ x).card+0 ≤ (outN D W x).card + share R ∅ x := by
    simpa [outN] using base x xw
  obtain ⟨K,kr,test⟩ := pair_feasible (T:=∅) (a:=0) (b:=0) rw' (empty_subset W)
    (by simp) base near.ge rW zw zr.symm (by simp) (by simp) rb zb
    (fun _ => rfl) (fun _ => rfl) (ax r rW) (ax z zw) (by simp [inter])
  exact ⟨K,kr,by simpa using test⟩

/-- Rows losing two heads in the four-label deletion. -/
def doubleRows (D : CH.Digraph) (U S : Finset ℕ) : Finset ℕ :=
  (U \ S).filter (fun r => (outN D S r).card = 2)

/-- At native order, if no row lost more than two heads and the common pool is
one short, every double-loss row has a head among the double-loss rows. -/
theorem native_no_sink {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : DeficitLevels.OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2)
    (sub : S ⊆ U) (four : S.card=4) (safe : QFree D (U \ S) 3) (hd : 2 ≤ d)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card = d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1=d) :
    ∀ r ∈ doubleRows D U S, (outN D (doubleRows D U S) r).Nonempty := by
  let W := U \ S
  let R := doubleRows D U S
  have rw' : R ⊆ W := filter_subset _ _
  have split (x) (xw : x ∈ W) : (outN D W x).card+(outN D S x).card=d+1 := by
    have eq : outN D W x = outN D U x \ outN D S x := by
      ext z; simp only [W,mem_outN,mem_sdiff]; tauto
    have incl : outN D S x ⊆ outN D U x := fun z h =>
      mem_outN.mpr ⟨sub (mem_outN.mp h).1,(mem_outN.mp h).2⟩
    rw [eq,card_sdiff_add_card_eq_card incl,exactRows x xw]
  have base (x) (xw : x ∈ W) : d ≤ (outN D W x).card+share R ∅ x := by
    have sum := split x xw
    by_cases mem : x ∈ R
    · have lost := (mem_filter.mp mem).2
      simp [share,mem]; omega
    · have ne : (outN D S x).card ≠ 2 := fun e => mem (mem_filter.mpr ⟨xw,e⟩)
      have bound := two x xw
      simp [share,mem]; omega
  intro r rr
  by_contra empty
  have eq : outN D R r = ∅ := not_nonempty_iff_eq_empty.mp empty
  have rsum := split r (rw' rr)
  have lost := (mem_filter.mp rr).2
  have rsize : (outN D W r).card + 1 = d := by omega
  obtain ⟨K,kr,test⟩ := sink_feasible safe hd rw' rr eq rsize base near
  exact critical_obstruction law size sub four safe K (kr.trans rw') (R \ K) (sdiff_subset.trans rw') test

/-- Rows forced to parent both copies. -/
def tripleRows (D : CH.Digraph) (U S : Finset ℕ) : Finset ℕ :=
  (U \ S).filter (fun r => (outN D S r).card = 3)

private theorem split_row {D : CH.Digraph} {U S : Finset ℕ} (sub : S ⊆ U) (x : ℕ) :
    (outN D (U \ S) x).card + (outN D S x).card = (outN D U x).card := by
  have eq : outN D (U \ S) x = outN D U x \ outN D S x := by
    ext z; simp only [mem_outN,mem_sdiff]; tauto
  have incl : outN D S x ⊆ outN D U x := fun z h =>
    mem_outN.mpr ⟨sub (mem_outN.mp h).1,(mem_outN.mp h).2⟩
  rw [eq,card_sdiff_add_card_eq_card incl]

/-- Every eligible pair misses the conflict budget in a native-order candidate.
The premises use the actual rows losing two or three heads to S. -/
theorem native_overlap {D : CH.Digraph} {U S : Finset ℕ} {d x z a b : ℕ}
    (law : DeficitLevels.OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2)
    (sub : S ⊆ U) (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ y ∈ U \ S, (outN D U y).card = d+1)
    (three : ∀ y ∈ U \ S, (outN D S y).card ≤ 3) :
    let W := U \ S
    let R := doubleRows D U S
    let T := tripleRows D U S
    let B := commonBank D W R T d
    d ≤ B.card+1 → x ∈ W → z ∈ W → x ≠ z → x ∉ T → z ∉ T → x ∉ B → z ∉ B →
    (x ∈ R → a=0) → (z ∈ R → b=0) →
    d + (outN D T x).card + a ≤ (outN D W x).card + share R T x →
    d + (outN D T z).card + b ≤ (outN D W z).card + share R T z →
    a+b < (signature D R x ∩ signature D R z).card := by
  intro W R T B near xw zw xz xt zt xb zb hx hz ax az
  have rw' : R ⊆ W := filter_subset _ _
  have tw : T ⊆ W := filter_subset _ _
  have rt : Disjoint R T := disjoint_left.mpr (fun y yr yt => by
    have h2 := (mem_filter.mp yr).2
    have h3 := (mem_filter.mp yt).2
    omega)
  have base (y) (yw : y ∈ W) : d ≤ (outN D W y).card + share R T y := by
    have sum := split_row (D:=D) sub y
    change (outN D W y).card+_=_ at sum
    rw [exactRows y yw] at sum
    have limit := three y yw
    by_cases yr : y ∈ R
    · have notT := disjoint_left.mp rt yr
      have lost := (mem_filter.mp yr).2
      simp [share,yr,notT]; omega
    by_cases yt : y ∈ T
    · have lost := (mem_filter.mp yt).2
      simp [share,yr,yt]; omega
    have n2 : (outN D S y).card ≠ 2 := fun e => yr (mem_filter.mpr ⟨yw,e⟩)
    have n3 : (outN D S y).card ≠ 3 := fun e => yt (mem_filter.mpr ⟨yw,e⟩)
    simp [share,yr,yt]; omega
  by_contra! overlap
  obtain ⟨K,kr,test⟩ := pair_feasible rw' tw rt base near xw zw xz xt zt xb zb hx hz ax az overlap
  exact critical_obstruction law size sub four safe _ (union_subset tw (kr.trans rw'))
    _ (union_subset tw (sdiff_subset.trans rw')) test

/-- Pairwise intersection on the actual double-loss rows at native order.
On a terminal class of these rows, both witnesses already lie in that class's
closed out-neighborhoods. -/
theorem native_closed_intersect {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : DeficitLevels.OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2)
    (sub : S ⊆ U) (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card = d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : d ≤ (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1) :
    let R := doubleRows D U S
    ∀ x ∈ R, ∀ z ∈ R, (insert x (outN D R x) ∩ insert z (outN D R z)).Nonempty := by
  intro R x xr z zr
  let W := U \ S
  have rw' : R ⊆ W := filter_subset _ _
  by_cases xz : x=z
  · subst z; exact ⟨x,mem_inter.mpr ⟨mem_insert_self _ _,mem_insert_self _ _⟩⟩
  have noT : tripleRows D U S = ∅ := eq_empty_iff_forall_notMem.mpr (by
    intro y yt
    obtain ⟨yw,h3⟩ := mem_filter.mp yt
    have := two y yw
    omega)
  have applyPair := native_overlap (x:=x) (z:=z) (a:=0) (b:=0) law size sub four safe exactRows
    (fun y yw => (two y yw).trans (by decide))
  dsimp only at applyPair
  rw [noT] at applyPair
  have notB (y) (yr : y ∈ R) : y ∉ commonBank D W R ∅ d :=
    fun h => (mem_sdiff.mp (mem_filter.mp h).1).2 (mem_union_right _ yr)
  have pays (y) (yr : y ∈ R) : d + (outN D ∅ y).card + 0 ≤ (outN D W y).card + share R ∅ y := by
    have sum := split_row (D:=D) sub y
    rw [exactRows y (rw' yr)] at sum
    change (outN D W y).card + _ = _ at sum
    have lost := (mem_filter.mp yr).2
    have emptyRow : outN D ∅ y = ∅ := by simp [outN]
    rw [emptyRow]
    simp [share,yr]
    omega
  have pos := applyPair near (rw' xr) (rw' zr) xz (by simp) (by simp)
    (notB x xr) (notB z zr) (fun _ => rfl) (fun _ => rfl) (pays x xr) (pays z zr)
  have sx : signature D R x = insert x (outN D R x) := by simp [signature,xr,union_comm]
  have sz : signature D R z = insert z (outN D R z) := by simp [signature,zr,union_comm]
  rw [← sx,← sz]
  exact card_pos.mp pos

#print axioms native_overlap
#print axioms native_closed_intersect
#print axioms sink_feasible
#print axioms native_no_sink
#print axioms split_pair
#print axioms pair_feasible
end LeanCH.BR.Closure.TwoReplacement.NearMiss
