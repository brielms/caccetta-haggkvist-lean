import checkpoints.shen_extension.JointShortcutReplay
import LeanCH.BR.BRTwoBallEquality

namespace LeanCH.BR.BackwardBallBank
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay

/-- Each small forward ball has a sink in its induced graph. Its entire row
lies in the next layer. Stop requiring growth once the ball exceeds q. -/
theorem capped_growth {D W q d} (free : QFree D W q)
    (degree : ∀ a ∈ W, d ≤ (outN D W a).card) {a} (aw : a ∈ W) (k : ℕ) :
    min (q+1) (1+k*d) ≤ (ball D W a k).card := by
  induction k with
  | zero => simpa using card_pos.mpr (nonempty_iff_ne_empty.mpr
      (ne_empty_of_mem (self_mem_ball (k:=0) aw)))
  | succ k ih =>
    let S := ball D W a k
    have inc : S ⊆ ball D W a (k+1) := ball_mono_radius (by omega)
    by_cases large : q < S.card
    · exact (min_le_left ..).trans (large.trans_le (card_le_card inc))
    obtain ⟨s,ss,sink⟩ := exists_sink (free.mono_set (ball_subset (D:=D) (W:=W)))
      ⟨a,self_mem_ball (k:=k) aw⟩ (Nat.le_of_not_gt large)
    have dis : Disjoint S (outN D W s) :=
      disjoint_left.mpr (fun y ys hy => sink y ys (mem_outN.mp hy).2)
    have more : S ∪ outN D W s ⊆ ball D W a (k+1) := union_subset inc fun y hy =>
      ball_step ss (outN_subset hy) (mem_outN.mp hy).2
    have total := card_le_card more
    rw [card_union_of_disjoint dis] at total
    have ds := degree s (ball_subset ss)
    change min (q+1) (1+k*d) ≤ S.card at ih
    rw [Nat.succ_mul]
    omega

/-- A selected bank in W contains its hub and lies in one native reverse
ball. Paths certifying membership may use any vertices of W. -/
theorem select_bank {D W q d b k} (free : QFree D W q) (live : W.Nonempty)
    (degree : ∀ a ∈ W, d ≤ (outN D W a).card) (pos : 0 < b)
    (cap : b ≤ q+1) (room : b ≤ 1+k*d) :
    ∃ h ∈ W, ∃ B ⊆ W, h ∈ B ∧ B.card = b ∧ B ⊆ reverseBall D W h k := by
  classical
  obtain ⟨h,hw,big⟩ : ∃ h ∈ W, b ≤ (reverseBall D W h k).card := by
    by_contra! small
    have lt := sum_lt_sum_of_nonempty live (fun a ha => (small a ha).trans_le
      ((le_min cap room).trans (capped_growth free degree ha k)))
    exact (ne_of_lt lt) (sum_reverseBall_eq_sum_ball D W k)
  have self : h ∈ reverseBall D W h k := mem_filter.mpr ⟨hw,self_mem_ball hw⟩
  obtain ⟨B,keep,inside,card⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr self)
    (by rw [card_singleton]; omega) big
  exact ⟨h,hw,B,inside.trans (filter_subset _ _),keep (mem_singleton_self _),card,inside⟩

structure Site (D : CH.Digraph) (V B : Finset ℕ) (h k : ℕ) : Prop where
  sub : B ⊆ V
  hub : h ∈ B
  before : ∀ a ∈ B, ∃ l ≤ k, Walk D V a h l

theorem all_heads_survive {D V B h k q} (site : Site D V B h k)
    (free : QFree D V q) (radius : k+1 ≤ q) :
    outN D (V \ B) h = outN D V h := by
  ext z
  simp only [mem_outN,mem_sdiff]
  refine ⟨fun ⟨⟨zv,_⟩,hz⟩ => ⟨zv,hz⟩,fun ⟨zv,hz⟩ => ⟨⟨zv,?_⟩,hz⟩⟩
  intro zb
  obtain ⟨l,le,w⟩ := site.before z zb
  exact free h (l+1) (by omega) (by omega) (.step zv hz w)

private theorem cut_row {D U t C u} (budget : (C u).card ≤ spare D U t u)
    (short : (outN (cut D C) U u).card < t) : outN (cut D C) U u = outN D U u := by
  have eq : outN (cut D C) U u = outN D U u \ C u := by
    ext z
    simp [mem_outN,cut,and_assoc]
  change (C u).card ≤ (outN D U u).card-t at budget
  have lost := card_le_card_sdiff_add_card (s:=outN D U u) (t:=C u)
  rw [eq] at short
  have : (C u).card = 0 := by omega
  simpa [card_eq_zero.mp this] using eq

private theorem debtor_to_hub {D V B h k t u} (site : Site D V B h k)
    (degree : t ≤ (outN D V u).card) (short : (outN D (V \ B) u).card < t) :
    ∃ l ≤ k+1, Walk D V u h l := by
  obtain ⟨a,hit,miss⟩ := exists_mem_notMem_of_card_lt_card (short.trans_le degree)
  obtain ⟨av,ua⟩ := mem_outN.mp hit
  have ab : a ∈ B := by
    by_contra off
    exact miss (mem_outN.mpr ⟨mem_sdiff.mpr ⟨av,off⟩,ua⟩)
  obtain ⟨l,le,w⟩ := site.before a ab
  exact ⟨l+1,by omega,.step av ua w⟩

/-- A native connector u ⇝ h turns any short retained path z ⇝ u into a
forbidden closed walk when z is a head of h. -/
theorem return_length {D K V U q h u z l i} (free : QFree D V q)
    (sub : ∀ a b, K a b = true → D a b = true) (uv : U ⊆ V)
    (zu : z ∈ U) (hz : D h z = true) (back : Walk D V u h i) (w : Walk K U z u l) :
    q ≤ l+i := by
  by_contra! low
  exact free h (l+i+1) (by omega) (by omega) (.step (uv zu) hz (((walk_sub sub w).mono uv).append back))

/-- The two or more new arcs of a mixed cycle cannot fit in the length budget.
The equivalence keeps each individual shortcut paired with its own tail. -/
theorem repair_iff {D K V U P q h a} {S : ℕ → Finset ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (sub : ∀ x y, K x y = true → D x y = true)
    (near : ∀ u ∈ P, ∃ i ≤ a, Walk D V u h i) (radius : 2*a ≤ q+1)
    (heads : ∀ u ∈ P, ∀ z ∈ S u, z ∈ U ∧ D h z = true) :
    QFree (DeleteRepair.repair K P S) U q ↔
      ∀ u ∈ P, ∀ z ∈ S u, ∀ l, l+1 ≤ q → ¬ Walk K U z u l := by
  constructor
  · intro safe u up z zs l bound path
    have w := walk_sub (fun x y edge => DeleteRepair.repair_old (P:=P) (S:=S) edge) path
    exact safe z (l+1) (by omega) bound (w.snoc (heads u up z zs).1 (DeleteRepair.repair_new up zs))
  · intro own
    apply DeleteRepair.repair_qfree_half (fun x l pos le w => free x l pos le ((walk_sub sub w).mono uv)) own
    intro u up z zs v vp l half walk
    obtain ⟨i,le,back⟩ := near v vp
    obtain ⟨zu,hz⟩ := heads u up z zs
    have := return_length free sub uv zu hz back walk
    omega

noncomputable def returns (D K : CH.Digraph) (U : Finset ℕ) (q h u : ℕ) :=
  (outN D U h \ outN D U u).filter (fun z => u ∈ ball K U z (q-1))

structure ReturnQuota (D : CH.Digraph) (V B : Finset ℕ) (q t h k : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ, (∀ a ∈ V \ B, (C a).card ≤ spare D (V \ B) t a) →
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (outN D V h ∪ outN D (V \ B) u).card + 1 ≤
        t + (returns D (cut D C) (V \ B) q h u).card ∧
      ∀ z ∈ returns D (cut D C) (V \ B) q h u, ∃ l, q ≤ l+k+1 ∧ l+1 ≤ q ∧
        Walk (cut D C) (V \ B) z u l

/-- On one cut install every eligible hub head that does not return to the
sending row. The row identity counts distinct physical heads exactly. -/
theorem install_all {D V B q t h k} (site : Site D V B h k) (free : QFree D V q)
    (degree : ∀ u ∈ V, t ≤ (outN D V u).card) (radius : 2*k+1 ≤ q)
    (C : ℕ → Finset ℕ) (budget : ∀ a ∈ V \ B, (C a).card ≤ spare D (V \ B) t a) :
    let U := V \ B
    let K := cut D C
    let P := U.filter (fun u => (outN D U u).card < t)
    let S := fun u => (outN D U h \ outN D U u) \ returns D K U q h u
    let E := DeleteRepair.repair K P S
    QFree E U q ∧
    (∀ u ∈ P, (outN E U u).card + (returns D K U q h u).card =
      (outN D V h ∪ outN D U u).card) ∧
    (∀ u ∈ U, u ∉ P → t ≤ (outN E U u).card) := by
  classical
  let U := V \ B
  let K := cut D C
  let P := U.filter (fun u => (outN D U u).card < t)
  let S := fun u => (outN D U h \ outN D U u) \ returns D K U q h u
  let E := DeleteRepair.repair K P S
  have near : ∀ u ∈ P, ∃ i ≤ k+1, Walk D V u h i := by
    intro u up
    obtain ⟨uu,low⟩ := mem_filter.mp up
    exact debtor_to_hub site (degree u (mem_sdiff.mp uu).1) low
  have head : ∀ u ∈ P, ∀ z ∈ S u, z ∈ U ∧ D h z = true :=
    fun _ _ _ zs => mem_outN.mp (mem_sdiff.mp (mem_sdiff.mp zs).1).1
  have good : QFree E U q := (repair_iff free sdiff_subset JointShortcut.cut_sub near (by omega) head).2 <| by
    intro u up z zs l bound w
    obtain ⟨cand,off⟩ := mem_sdiff.mp zs
    exact off (mem_filter.mpr ⟨cand,mem_ball.mpr ⟨(mem_filter.mp up).1,l,by omega,w⟩⟩)
  refine ⟨good,?_,?_⟩
  · intro u up
    have uu : u ∈ U := (mem_filter.mp up).1
    have low : (outN D U u).card < t := (mem_filter.mp up).2
    have kb : outN K U u ⊆ outN D U u := fun _ hit =>
      mem_outN.mpr ⟨(mem_outN.mp hit).1,JointShortcut.cut_sub _ _ (mem_outN.mp hit).2⟩
    have eq := cut_row (budget u uu) ((card_le_card kb).trans_lt low)
    have row : outN E U u = outN K U u ∪ S u := by
      ext z
      constructor
      · intro hit
        obtain old | new := DeleteRepair.repair_cases (mem_outN.mp hit).2
        · exact mem_union_left _ (mem_outN.mpr ⟨outN_subset hit,old⟩)
        · exact mem_union_right _ new.2
      · intro hit
        obtain old | new := mem_union.mp hit
        · exact mem_outN.mpr ⟨outN_subset old,DeleteRepair.repair_old (mem_outN.mp old).2⟩
        · exact mem_outN.mpr ⟨(head _ up _ new).1,DeleteRepair.repair_new up new⟩
    have dis : Disjoint (outN D U u) (S u) := disjoint_left.mpr
      (fun z hz zs => (mem_sdiff.mp (mem_sdiff.mp zs).1).2 hz)
    have cost := card_sdiff_add_card_eq_card (filter_subset
      (fun z => u ∈ ball K U z (q-1)) (outN D U h \ outN D U u))
    change (S u).card + (returns D K U q h u).card = _ at cost
    have parts := card_sdiff_add_card (outN D U h) (outN D U u)
    change (outN E U u).card + _ = _
    rw [row,eq,card_union_of_disjoint dis,← all_heads_survive site free (by omega)]
    change (outN D U u).card + (S u).card + (returns D K U q h u).card =
      (outN D U h ∪ outN D U u).card
    omega
  · intro u uu off
    have lo : t ≤ (outN K U u).card := by
      by_contra! bad
      exact off (mem_filter.mpr ⟨uu,(cut_row (budget u uu) bad) ▸ bad⟩)
    exact lo.trans (card_le_card fun z hit =>
      mem_outN.mpr ⟨outN_subset hit,DeleteRepair.repair_old (mem_outN.mp hit).2⟩)

theorem quota {D V B h k q t} (site : Site D V B h k) (bank : Eligible V B q t)
    (free : QFree D V q) (none : NoHost q t) (degree : ∀ u ∈ V, t ≤ (outN D V u).card)
    (radius : 2*k+1 ≤ q) : ReturnQuota D V B q t h k := by
  classical
  constructor
  intro C budget
  let U := V \ B
  let K := cut D C
  let A := fun u => (outN D U h \ outN D U u) \ returns D K U q h u
  let P := U.filter (fun u => (outN D U u).card < t)
  let E := DeleteRepair.repair K P A
  obtain ⟨safe,rows,other⟩ := install_all site free degree radius C budget
  have size := card_sdiff_add_card_eq_card bank.sub
  have cap := bank.size
  have stuck := none E U bank.live (by dsimp [U]; omega) safe
  push Not at stuck
  obtain ⟨u,uu,low⟩ := stuck
  have up : u ∈ P := by
    by_contra off
    exact (not_lt_of_ge (other u uu off)) low
  have short : (outN D U u).card < t := (mem_filter.mp up).2
  obtain ⟨i,le,back⟩ := debtor_to_hub site (degree u (mem_sdiff.mp uu).1) short
  refine ⟨u,uu,short,?_,?_⟩
  · have row := rows u up
    change (outN E U u).card + (returns D K U q h u).card = (outN D V h ∪ outN D U u).card at row
    change (outN D V h ∪ outN D U u).card + 1 ≤ t + (returns D K U q h u).card
    omega
  · intro z returned
    obtain ⟨cand,ballHit⟩ := mem_filter.mp returned
    obtain ⟨zu,hz⟩ := mem_outN.mp (mem_sdiff.mp cand).1
    obtain ⟨_,l,bound,w⟩ := mem_ball.mp ballHit
    have := return_length free JointShortcut.cut_sub sdiff_subset zu hz back w
    exact ⟨l,by omega,by omega,w⟩

/-- One bank and hub work for every subsequent budgeted cut. A is a specified
set of protected physical labels; the new bank avoids all of them. -/
structure Supply (D : CH.Digraph) (V A : Finset ℕ) (q t b k : ℕ) : Prop where
  acquire : ∃ B h, Disjoint B A ∧ B.card = b ∧ Site D V B h k ∧ Eligible V B q t ∧
    outN D (V \ B) h = outN D V h ∧ ReturnQuota D V B q t h k

theorem protected_supply {D V A q t b k d} (free : QFree D V q) (none : NoHost q t)
    (degree : ∀ u ∈ V, t ≤ (outN D V u).card) (positive : 0 < t)
    (live : (V \ A).Nonempty) (away : ∀ u ∈ V \ A, d ≤ (outN D (V \ A) u).card)
    (pos : 0 < b) (cap : b ≤ q+1) (room : b ≤ 1+k*d)
    (size : V.card - q*t ≤ b) (radius : 2*k+1 ≤ q) : Supply D V A q t b k := by
  obtain ⟨h,hw,B,bw,hb,card,inside⟩ := select_bank (free.mono_set sdiff_subset) live away pos cap room
  have bv : B ⊆ V := bw.trans sdiff_subset
  have site : Site D V B h k := ⟨bv,hb,by
    intro a ab
    obtain ⟨_,hit⟩ := mem_filter.mp (inside ab)
    obtain ⟨_,l,le,w⟩ := mem_ball.mp hit
    exact ⟨l,le,w.mono sdiff_subset⟩⟩
  have heads := all_heads_survive site free (by omega)
  have nonempty : (V \ B).Nonempty := by
    have high := degree h (mem_sdiff.mp hw).1
    rw [← heads] at high
    obtain ⟨z,hit⟩ := card_pos.mp (positive.trans_le high)
    exact ⟨z,outN_subset hit⟩
  have bank : Eligible V B q t := ⟨bv,card ▸ size,nonempty⟩
  exact ⟨B,h,disjoint_left.mpr (fun _ hit => (mem_sdiff.mp (bw hit)).2),card,
    site,bank,heads,quota site bank free none degree radius⟩

theorem degree_away {D : CH.Digraph} {V A : Finset ℕ} (u : ℕ) :
    (outN D V u).card ≤ (outN D (V \ A) u).card + A.card := by
  have eq : outN D (V \ A) u = outN D V u \ A := by
    ext z
    simp only [mem_sdiff,mem_outN]
    tauto
  rw [eq]
  exact card_le_card_sdiff_add_card

/-- Three available native heads outside the protected labels suffice for
every cutoff q ≥ 3 and every bank size up to q. Return the smallest radius
supported by the actual lower degree away from those labels. -/
theorem quota_drop {D V A q r b} (free : QFree D V q) (none : NoHost q (r-1))
    (live : V.Nonempty) (degree : ∀ u ∈ V, r ≤ (outN D V u).card)
    (hq : 3 ≤ q) (keep : A.card+3 ≤ r) (pos : 0 < b) (cap : b ≤ q)
    (size : V.card-q*(r-1) ≤ b) :
    ∃ k, 2*k+1 ≤ q ∧ b ≤ 1+k*(r-A.card) ∧
      (∀ j < k, 1+j*(r-A.card) < b) ∧ Supply D V A q (r-1) b k := by
  classical
  let d := r-A.card
  have three : 3 ≤ d := by dsimp [d]; omega
  have feasible : b ≤ 1+((q-1)/2)*d := by
    have grown := Nat.mul_le_mul_left ((q-1)/2) three
    omega
  have ex : ∃ k, b ≤ 1+k*d := ⟨_,feasible⟩
  let k := Nat.find ex
  have bounded : k ≤ (q-1)/2 := Nat.find_min' ex feasible
  have near : 2*k+1 ≤ q := by omega
  have nonempty : (V \ A).Nonempty := by
    obtain ⟨u,uv⟩ := live
    have le := (degree u uv).trans (card_le_card (outN_subset : outN D V u ⊆ V))
    exact sdiff_nonempty_of_card_lt_card (by omega)
  have away : ∀ u ∈ V \ A, d ≤ (outN D (V \ A) u).card := by
    intro u uw
    have lo := degree u (mem_sdiff.mp uw).1
    have loss := degree_away (D:=D) (V:=V) (A:=A) u
    dsimp [d]; omega
  exact ⟨k,near,Nat.find_spec ex,fun j smaller => Nat.lt_of_not_ge (Nat.find_min ex smaller),
    protected_supply free none (fun u uv => (Nat.sub_le r 1).trans (degree u uv))
      (by omega) nonempty away pos (by omega) (Nat.find_spec ex) size near⟩

theorem distinct_returns {D V B h k q t r} (paid : ReturnQuota D V B q t h k)
    (deg : r ≤ (outN D V h).card) (C : ℕ → Finset ℕ)
    (budget : ∀ a ∈ V \ B, (C a).card ≤ spare D (V \ B) t a) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      r+1 ≤ t + (returns D (cut D C) (V \ B) q h u).card ∧
      ∀ z ∈ returns D (cut D C) (V \ B) q h u, ∃ l, q ≤ l+k+1 ∧ l+1 ≤ q ∧
        Walk (cut D C) (V \ B) z u l := by
  obtain ⟨u,uu,short,score,paths⟩ := paid.at_cut C budget
  have le := card_le_card (subset_union_left (s₂:=outN D (V \ B) u) : outN D V h ⊆ _)
  exact ⟨u,uu,short,by omega,paths⟩

/-- One native source can be queried with different protected labels. The
new bank has the specified size. Nothing identifies its debtor with a debtor
of the earlier bank. -/
structure ProtectedBanks (D : CH.Digraph) (V : Finset ℕ) (q r b : ℕ) : Prop where
  choose : ∀ A : Finset ℕ, A.card + 3 ≤ r → ∃ k, 2*k+1 ≤ q ∧
    b ≤ 1+k*(r-A.card) ∧ (∀ j < k, 1+j*(r-A.card) < b) ∧ Supply D V A q (r-1) b k

@[aesop safe forward (immediate := [cell,none,hq,order,cover]) (rule_sets := [CHGraphFamilies])]
theorem on_marked_source {q r n} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (none : NoHost q (r-1)) (hq : 3 ≤ q)
    (order : X.V.card ≤ n) (cover : n ≤ q*r) :
    ProtectedBanks X.D X.V q r m.bank.card := by
  constructor
  intro A room
  have size := cell.size
  have hr : r = r-1+1 := by omega
  have product : q*r = q*(r-1)+q := by conv_lhs => rw [hr, Nat.mul_add, Nat.mul_one]
  exact quota_drop X.free none X.nonempty X.degree hq room
    (card_pos.mpr ⟨m.parent,cell.erased⟩) (by omega) (by omega)

/-- Move a specified surviving label into this bank in exchange for an
erased label other than the hub. A native route to the very same hub is the
only new reach premise. Recompute the quota on the new survivors. -/
theorem exchange {D V B q t h k a v} (site : Site D V B h k)
    (bank : Eligible V B q t) (free : QFree D V q) (none : NoHost q t)
    (degree : ∀ u ∈ V, t ≤ (outN D V u).card) (radius : 2*k+1 ≤ q)
    (ab : a ∈ B) (ah : a ≠ h) (vs : v ∈ V \ B)
    (near : ∃ l ≤ k, Walk D V v h l) :
    let B' := insert v (B.erase a)
    B'.card = B.card ∧ a ∈ V \ B' ∧ Site D V B' h k ∧
      Eligible V B' q t ∧ ReturnQuota D V B' q t h k := by
  classical
  obtain ⟨vv,vb⟩ := mem_sdiff.mp vs
  let B' := insert v (B.erase a)
  have va : v ≠ a := fun eq => vb (eq ▸ ab)
  have card : B'.card = B.card := by
    dsimp [B']
    rw [card_insert_of_notMem (fun hit => vb (mem_of_mem_erase hit)),card_erase_of_mem ab]
    have pos := card_pos.mpr ⟨a,ab⟩
    omega
  have kept : a ∈ V \ B' := mem_sdiff.mpr ⟨site.sub ab, by simp [B',va.symm]⟩
  have site' : Site D V B' h k := ⟨insert_subset vv ((erase_subset _ _).trans site.sub),
    mem_insert_of_mem (mem_erase.mpr ⟨Ne.symm ah,site.hub⟩),by
      intro x xb
      rcases mem_insert.mp xb with rfl | old
      · exact near
      · exact site.before x (mem_of_mem_erase old)⟩
  have bank' : Eligible V B' q t := ⟨site'.sub,card.symm ▸ bank.size,⟨a,kept⟩⟩
  exact ⟨card,kept,site',bank',quota site' bank' free none degree radius⟩

/-- A debtor eligible for exchange has no return at the lowest possible
length in the general quota. Conversely an equality-length return pins
that debtor outside the hub's radius-k native reverse ball. -/
theorem shortest_excludes_exchange {D K V B q h k u z l}
    (free : QFree D V q) (sub : ∀ a b, K a b = true → D a b = true)
    (zu : z ∈ V \ B) (hz : D h z = true) (path : Walk K (V \ B) z u l)
    (tight : l+k+1 = q) : ¬ ∃ i ≤ k, Walk D V u h i := by
  rintro ⟨i,le,back⟩
  have := return_length free sub sdiff_subset zu hz back path
  omega

/-- An early row cannot lose a head to the bank: that head would return
to the hub soon enough to close a native walk. -/
theorem early_row {D V B h k q j x} (site : Site D V B h k)
    (free : QFree D V q) (early : x ∈ ball D V h j) (room : j+k+1 ≤ q) :
    outN D (V \ B) x = outN D V x := by
  obtain ⟨_,i,ij,front⟩ := mem_ball.mp early
  ext y
  simp only [mem_outN,mem_sdiff]
  refine ⟨fun ⟨⟨yv,_⟩,xy⟩ => ⟨yv,xy⟩,fun ⟨yv,xy⟩ => ⟨⟨yv,?_⟩,xy⟩⟩
  intro yb
  obtain ⟨l,lk,back⟩ := site.before y yb
  exact free h (i+1+l) (by omega) (by omega) ((front.snoc yv xy).append back)

/-- A nonterminal in the cascade has more live next labels than its budget,
including when it first entered at an earlier stage. -/
theorem active_heads {D U P e x i} (onPath : x ∈ active D U P e (i+1))
    (outside : x ∉ P) : e x < (outN D (active D U P e i) x).card := by
  induction i with
  | zero =>
    rcases mem_union.mp onPath with old | rich
    · exact (outside old).elim
    · exact (mem_filter.mp rich).2
  | succ i ih =>
    rcases mem_union.mp onPath with old | rich
    · apply lt_of_lt_of_le (ih old) (card_le_card ?_)
      intro y hy
      exact mem_outN.mpr ⟨active_mono D U P e (Nat.le_succ i) (mem_outN.mp hy).1,
        (mem_outN.mp hy).2⟩
    · exact (mem_filter.mp rich).2

def shortRows (D : CH.Digraph) (U : Finset ℕ) (t : ℕ) := U.filter (fun u => (outN D U u).card < t)

/-- The next native forward layer and the preceding cascade stage are on
the same physical labels, so this implication can be applied at each child
as long as its radius permits. -/
theorem early_branches {D V B h k q r t x i j} (site : Site D V B h k)
    (free : QFree D V q) (degree : ∀ a ∈ V, r ≤ (outN D V a).card) (tr : t ≤ r)
    (early : x ∈ ball D V h j) (room : j+k+1 ≤ q)
    (onPath : x ∈ active D (V \ B) (shortRows D (V \ B) t) (spare D (V \ B) t) (i+1)) :
    let live := active D (V \ B) (shortRows D (V \ B) t) (spare D (V \ B) t) i
    r+1 ≤ t+(outN D live x).card ∧ outN D live x ⊆ ball D V h (j+1) := by
  have lo := degree x (ball_subset early)
  rw [← early_row site free early room] at lo
  have outside : x ∉ shortRows D (V \ B) t := fun hit => (not_lt_of_ge (tr.trans lo)) (mem_filter.mp hit).2
  have branches := active_heads onPath outside
  change (outN D (V \ B) x).card-t < _ at branches
  refine ⟨by omega,?_⟩
  intro y hy
  have memU := active_sub D (V \ B) _ _ (filter_subset _ _) i (outN_subset hy)
  exact ball_step early (mem_sdiff.mp memU).1 (mem_outN.mp hy).2

/-- On the canonical affordable cut, many specific hub heads return to one
short row. For each such head the live first hops branch, and at least one
of those very first hops continues to the named row on that cut. -/
theorem same_row_forks {D V B h k q t r} (site : Site D V B h k) (free : QFree D V q)
    (paid : ReturnQuota D V B q t h k) (degree : ∀ a ∈ V, r ≤ (outN D V a).card)
    (tr : t ≤ r) (room : k+2 ≤ q) :
    let U := V \ B
    let P := shortRows D U t
    let e := spare D U t
    let C := fun a => bill D U P e a (q-1)
    let next := active D U P e (q-2)
    ∃ u ∈ P, r+1 ≤ t+(returns D (cut D C) U q h u).card ∧
      ∀ z ∈ returns D (cut D C) U q h u,
        r+1 ≤ t+(outN D next z).card ∧
        ∃ y ∈ outN D next z, (cut D C) z y = true ∧
          ∃ l, q ≤ l+k+2 ∧ l+2 ≤ q ∧ Walk (cut D C) U y u l := by
  let U := V \ B
  let P := shortRows D U t
  let e := spare D U t
  let C := fun a => bill D U P e a (q-1)
  obtain ⟨u,uu,low,count,paths⟩ := distinct_returns paid (degree h (site.sub site.hub)) C
    (fun a _ => affordable D U P e a (q-1))
  have up : u ∈ P := mem_filter.mpr ⟨uu,low⟩
  refine ⟨u,up,count,?_⟩
  intro z hit
  obtain ⟨l,minLen,maxLen,path⟩ := paths z hit
  obtain ⟨zu,hz⟩ := mem_outN.mp (mem_sdiff.mp (mem_filter.mp hit).1).1
  have early : z ∈ ball D V h 1 := ball_step (self_mem_ball (k:=0) (site.sub site.hub)) (mem_sdiff.mp zu).1 hz
  have rich := degree z (mem_sdiff.mp zu).1
  rw [← early_row site free early (by omega)] at rich
  have diff : z ≠ u := by rintro rfl; omega
  have az : z ∈ active D U P e ((q-2)+1) := active_mono D U P e (by omega)
    (sound_cut D U P e zu up (by omega : l ≤ q-1) path)
  refine ⟨(early_branches site free degree tr early (by omega) az).1,?_⟩
  cases path with
  | refl => exact (diff rfl).elim
  | @step z y u l yu zy suffix =>
    have ya := active_mono D U P e (show l ≤ q-2 by omega)
      (sound_cut D U P e yu up (by omega : l ≤ q-1) suffix)
    exact ⟨y,mem_outN.mpr ⟨ya,JointShortcut.cut_sub _ _ zy⟩,zy,l,by omega,by omega,suffix⟩

/-- An affordable cut controlling the own-return counts for every deficient
row contradicts the no-host quota on this very bank. -/
theorem close_by_counts {D V B q t h k} (paid : ReturnQuota D V B q t h k)
    (C : ℕ → Finset ℕ) (budget : ∀ a ∈ V \ B, (C a).card ≤ spare D (V \ B) t a)
    (counts : ∀ u ∈ V \ B, (outN D (V \ B) u).card < t →
      t + (returns D (cut D C) (V \ B) q h u).card ≤ (outN D V h ∪ outN D (V \ B) u).card) :
    False := by
  obtain ⟨u,uu,short,lower,_⟩ := paid.at_cut C budget
  have upper := counts u uu short
  omega

#print axioms early_row
#print axioms active_heads
#print axioms early_branches
#print axioms same_row_forks
#print axioms close_by_counts
#print axioms on_marked_source
#print axioms exchange
#print axioms shortest_excludes_exchange

#print axioms protected_supply
#print axioms quota_drop
#print axioms distinct_returns
#print axioms capped_growth
#print axioms select_bank
#print axioms repair_iff
#print axioms install_all
#print axioms quota
end LeanCH.BR.BackwardBallBank
