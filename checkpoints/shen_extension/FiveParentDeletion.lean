import checkpoints.shen_extension.BankReturnRectangles
import LeanCH.BR.BROutUniformContraction

namespace LeanCH.BR.ShenPuncture.FiveParent
open BRq2 BRq3 Finset WeightedSD BRsub

private theorem triangle {D V a b c} (free : QFree D V 3)
    (ha : a∈V) (hb : b∈V) (hc : c∈V)
    (ab : D a b=true) (bc : D b c=true) : D c a≠true := by
  intro ca
  exact free a 3 (by decide) le_rfl (.step hb ab (.step hc bc (.step ha ca (.refl a))))

/-- Delete r and fill a with z. Each full middle row can cut its edge to a.
Only the possible tight middle q has to be paid by the destination z. -/
theorem must_share_with_one_return {D : CH.Digraph} {V : Finset ℕ} {d r a q z : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ x∈V, d≤(outN D V x).card)
    (hr : r∈V) (ha : a∈V) (hz : z∈V) (ar : D a r=true) (rz : D r z=true)
    (parentR : ∀ x∈V, (outN D V x).card=d → D x r=true → x=a)
    (parentA : ∀ x∈V, (outN D V x).card=d → D x a=true → D z x=true → x=q)
    (room : d<(outN D V z).card ∨ D z q≠true) : D a z=true := by
  classical
  by_contra missing
  let W := V.erase r
  let C : CH.Digraph := fun x v => if (x=z ∧ v=q) ∨ (x≠q ∧ D z x=true ∧ v=a)
    then false else D x v
  let F := insertArc C a z
  have sub (x v) (e : C x v=true) : D x v=true := by
    dsimp [C] at e
    split at e <;> simp_all
  have arNe : a≠r := fun eq => loopfree free (by decide) hr (eq ▸ ar)
  have zr : z≠r := fun eq => loopfree free (by decide) hr (eq ▸ rz)
  have za : z≠a := fun eq => digonfree free (by decide) ha hr ar (eq ▸ rz)
  have noZA := triangle free ha hr hz ar rz
  have noZR := digonfree free (by decide) hr hz rz
  have aw : a∈W := mem_erase.mpr ⟨arNe,ha⟩
  have zw : z∈W := mem_erase.mpr ⟨zr,hz⟩
  have fc : QFree C W 3 := (qfree_sub sub free).mono_set (erase_subset _ _)
  have noTwo {m} (e : C z m=true) (f : C m a=true) : False := by
    by_cases mq : m=q
    · simp [C,mq] at e
    · have zm := sub _ _ e
      simp [C,mq,zm] at f
  have safe : a∉ball C W z 2 := by
    intro reach
    obtain ⟨_,j,hj,walk⟩ := mem_ball.mp reach
    interval_cases j
    · cases walk; exact za rfl
    · cases walk with
      | step _ e rest => cases rest; exact noZA (sub _ _ e)
    · cases walk with
      | step hm e rest => cases rest with
        | step _ f rest =>
          cases rest
          exact noTwo e f
  have ff : QFree F W 3 := qfree_insertArc fc ⟨a,aw⟩ ⟨z,zw⟩ safe
  have wc : W.card=V.card-1 := card_erase_of_mem hr
  apply (bankLaw_iff d).mp law F W ff ⟨a,aw⟩ (by omega)
  intro x hx
  have xu := mem_of_mem_erase hx
  have deg := degree x xu
  let old := outN D V x
  let new := outN F W x
  change d≤new.card
  have keep {v} (hit : v∈old) (vr : v≠r) (first : ¬(x=z ∧ v=q))
      (second : ¬(x≠q ∧ D z x=true ∧ v=a)) : v∈new := by
    have no := not_or.mpr ⟨first,second⟩
    have cv : C x v=true := by
      dsimp only [C]
      split
      · contradiction
      · exact (mem_outN.mp hit).2
    exact mem_outN.mpr ⟨mem_erase.mpr ⟨vr,outN_subset hit⟩,insertArc_mono C a z x v cv⟩
  have spare {b} (rich : d<old.card) (incl : old.erase b⊆new) : d≤new.card := by
    have le := card_le_card incl
    by_cases hit : b∈old
    · rw [card_erase_of_mem hit] at le; omega
    · rw [erase_eq_of_notMem hit] at le; omega
  by_cases xa : x=a
  · subst x
    have incl : insert z (old.erase r) ⊆ new := by
      intro v h
      rcases mem_insert.mp h with rfl | hit
      · exact mem_outN.mpr ⟨zw,by simp [F,insertArc]⟩
      · exact keep (mem_of_mem_erase hit) (mem_erase.mp hit).1
          (fun eq => za eq.1.symm) (fun eq => noZA eq.2.1)
    have fresh : z∉old.erase r := fun hit => missing (mem_outN.mp (mem_of_mem_erase hit)).2
    have le := card_le_card incl
    have hit : r∈old := mem_outN.mpr ⟨hr,ar⟩
    rw [card_insert_of_notMem fresh,card_erase_of_mem hit] at le
    change d≤old.card at deg
    omega
  by_cases small : old.card=d
  · have nr : D x r≠true := fun e => xa (parentR x xu small e)
    apply deg.trans (card_le_card (show old⊆new from ?_))
    intro v hit
    have edge := (mem_outN.mp hit).2
    apply keep hit (fun eq => nr (eq ▸ edge))
    · rintro ⟨rfl,rfl⟩
      rcases room with rich | absent
      · change (outN D V x).card=d at small; omega
      · exact absent edge
    · rintro ⟨nq,zx,rfl⟩
      exact nq (parentA x xu small edge zx)
  have rich : d<old.card := by change d≤old.card at deg; omega
  by_cases xr : D x r=true
  · apply spare (b:=r) rich
    intro v hit
    exact keep (mem_of_mem_erase hit) (mem_erase.mp hit).1
      (fun eq => noZR (eq.1 ▸ xr)) (fun eq => triangle free hr hz xu rz eq.2.1 xr)
  have vr {v} (hit : v∈old) : v≠r := fun eq => xr (eq ▸ (mem_outN.mp hit).2)
  by_cases xz : x=z
  · apply spare (b:=q) rich
    intro v hit
    have mem := mem_of_mem_erase hit
    exact keep mem (vr mem) (fun eq => (mem_erase.mp hit).1 eq.2)
      (fun eq => loopfree free (by decide) hz (xz ▸ eq.2.1))
  · apply spare (b:=a) rich
    intro v hit
    have mem := mem_of_mem_erase hit
    exact keep mem (vr mem) (fun eq => xz eq.1) (fun eq => (mem_erase.mp hit).1 eq.2.2)

theorem must_share {D : CH.Digraph} {V : Finset ℕ} {d r a q z : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ x∈V, d≤(outN D V x).card)
    (hr : r∈V) (ha : a∈V) (hz : z∈V) (ar : D a r=true) (rz : D r z=true)
    (parentR : ∀ x∈V, (outN D V x).card=d → D x r=true → x=a)
    (parentA : ∀ x∈V, (outN D V x).card=d → D x a=true → x=q)
    (room : d<(outN D V z).card ∨ D z q≠true) : D a z=true :=
  must_share_with_one_return free size law degree hr ha hz ar rz parentR
    (fun x h e f _ => parentA x h e f) room

/-- At the new common parent x, reroot the deletion one step farther.
If a full head f is not shared with q, it must point to BOTH blockers. -/
theorem reroot_full_head {D : CH.Digraph} {V : Finset ℕ} {d x q f u v : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ z∈V, d≤(outN D V z).card)
    (hx : x∈V) (hq : q∈V) (hf : f∈V) (qx : D q x=true) (xf : D x f=true)
    (parentX : ∀ z∈V, (outN D V z).card=d → D z x=true → z=q)
    (parentQ : ∀ z∈V, (outN D V z).card=d → D z q=true → z=u ∨ z=v)
    (rich : d<(outN D V f).card) (missing : D q f≠true) :
    D f u=true ∧ D f v=true := by
  constructor
  · by_contra miss
    apply missing (must_share_with_one_return (q:=v) free size law degree hx hq hf qx xf parentX ?_ (.inl rich))
    intro z hz deg zq fz
    exact (parentQ z hz deg zq).resolve_left (fun eq => miss (eq ▸ fz))
  · by_contra miss
    apply missing (must_share_with_one_return (q:=u) free size law degree hx hq hf qx xf parentX ?_ (.inl rich))
    intro z hz deg zq fz
    exact (parentQ z hz deg zq).resolve_right (fun eq => miss (eq ▸ fz))

#print axioms must_share
#print axioms reroot_full_head

/-- At the five-parent endpoint, reroot the single-parent repair at w.
The exceptional tight heads that can refuse to share are already heads of y. -/
theorem nested_rows {D : CH.Digraph} {V : Finset ℕ} {d w y a q : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ x∈V, d≤(outN D V x).card)
    (ha : a∈V) (hy : y∈V) (yw : w∈outN D V y) (aw : D a w=true)
    (wydeg : (outN D V w).card=d) (ydeg : (outN D V y).card=d+1)
    (parentW : ∀ x∈V, (outN D V x).card=d → D x w=true → x=a)
    (parentA : ∀ x∈V, (outN D V x).card=d → D x a=true → x=q)
    (headsA : outN D V a ⊆ insert y (outN D V y))
    (intoQ : ∀ x∈V, (outN D V x).card=d → D x q=true → x∈outN D V y) :
    outN D V w=(outN D V y).erase w := by
  have hw := outN_subset yw
  apply eq_of_subset_of_card_le
  · intro z hit
    have hz := outN_subset hit
    have wz := (mem_outN.mp hit).2
    refine mem_erase.mpr ⟨fun eq => loopfree free (by decide) hw (eq ▸ wz),?_⟩
    by_contra absent
    have miss : D a z≠true := by
      intro az
      rcases mem_insert.mp (headsA (mem_outN.mpr ⟨hz,az⟩)) with rfl | e
      · exact digonfree free (by decide) hy hw (mem_outN.mp yw).2 wz
      · exact absent e
    have fail := fun room => miss (must_share free size law degree hw ha hz aw wz parentW parentA room)
    have full : ¬d<(outN D V z).card := fun high => fail (.inl high)
    have zq : D z q=true := by by_contra no; exact fail (.inr no)
    exact absent (intoQ z hz (le_antisymm (by omega) (degree z hz)) zq)
  · rw [card_erase_of_mem yw,ydeg,wydeg]; omega

#print axioms nested_rows

/-- Every return middle fed by the blocker retains its whole row under
either deletion. This applies to the tight middle q as well as to full ones. -/
theorem same_payers {D : CH.Digraph} {V : Finset ℕ} {w y b x : ℕ}
    (free : QFree D V 3) (hy : y∈V) (hw : w∈V) (hb : b∈V) (hx : x∈V)
    (yb : D y b=true) (wb : D w b=true) (bx : D b x=true) :
    outN D (V.erase y) x=outN D V x ∧ outN D (V.erase w) x=outN D V x := by
  have keep (r) (no : D x r≠true) : outN D (V.erase r) x=outN D V x := by
    ext j
    simp only [mem_outN,mem_erase]
    constructor
    · rintro ⟨⟨_,hj⟩,e⟩; exact ⟨hj,e⟩
    · rintro ⟨hj,e⟩; exact ⟨⟨fun eq => no (eq ▸ e),hj⟩,e⟩
  exact ⟨keep y (triangle free hy hb hx yb bx),keep w (triangle free hw hb hx wb bx)⟩

/-- Deleting a,q,y,w at once forces a common full parent of a,y,w. This
vertex is itself a head of q. The alternatives in dom express domination by
the five tight rows: both blockers are heads of y and of w. -/
theorem forced_triple_parent {D : CH.Digraph} {V : Finset ℕ} {d a q y w : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (large : 4<V.card)
    (law : BankLaw (d-1)) (degree : ∀ x∈V, d≤(outN D V x).card)
    (ha : a∈V) (hq : q∈V) (hy : y∈V) (hw : w∈V)
    (four : ({a,q,y,w}:Finset ℕ).card=4)
    (nested : outN D V w=(outN D V y).erase w)
    (headsA : outN D V a ⊆ insert y (outN D V y))
    (dom : ∀ x∈V, ∃ p∈V, D p x=true ∧
      (p=q ∨ p=a ∨ p=w ∨ (D y p=true ∧ D w p=true)))
    (parents : ∀ x∈V, (outN D V x).card=d →
      (D x a=true → x=q) ∧ (D x y=true → x=a) ∧ (D x w=true → x=a)) :
    ∃ x∈V \ {a,q,y,w}, d<(outN D V x).card ∧ D q x=true ∧
      D x a=true ∧ D x y=true ∧ D x w=true := by
  classical
  let C : Finset ℕ := {a,q,y,w}
  let X := V \ C
  have sub : C⊆V := insert_subset ha (insert_subset hq (insert_subset hy (singleton_subset_iff.mpr hw)))
  have sz := card_sdiff_add_card_eq_card sub
  change X.card+C.card=V.card at sz
  change C.card=4 at four
  have split {x} (hx : x∈X) :
      D q x=true ∨ (D x y≠true ∧ D x w≠true) := by
    have xv := (mem_sdiff.mp hx).1
    have outside := (mem_sdiff.mp hx).2
    have xw : x≠w := fun eq => outside (by simp [C,eq])
    have xy : x≠y := fun eq => outside (by simp [C,eq])
    have both (h : x∈outN D V y) : D x y≠true ∧ D x w≠true := by
      have h' : x∈outN D V w := nested ▸ mem_erase.mpr ⟨xw,h⟩
      exact ⟨digonfree free (by decide) hy xv (mem_outN.mp h).2,
        digonfree free (by decide) hw xv (mem_outN.mp h').2⟩
    obtain ⟨p,pv,e,rfl|rfl|rfl|⟨yp,wp⟩⟩ := dom x xv
    · exact .inl e
    · exact .inr (both ((mem_insert.mp (headsA (mem_outN.mpr ⟨xv,e⟩))).resolve_left xy))
    · have hit := mem_outN.mpr ⟨xv,e⟩
      exact .inr (both (mem_of_mem_erase (nested ▸ hit)))
    · exact .inr ⟨triangle free hy pv xv yp e,triangle free hw pv xv wp e⟩
  by_contra none
  apply (bankLaw_iff _).mp law D X (free.mono_set sdiff_subset)
    (card_pos.mp (by omega)) (by omega)
  intro x hx
  have xv := (mem_sdiff.mp hx).1
  have out := (mem_sdiff.mp hx).2
  let O := outN D V x
  have loss := card_sdiff_add_card_inter O C
  have row : outN D X x=O \ C := by ext j; simp only [X,O,mem_outN,mem_sdiff]; tauto
  rw [row]
  have deg : d≤O.card := degree x xv
  have bound {S : Finset ℕ} (h : ∀ j∈C, D x j=true → j∈S) : (O ∩ C).card≤S.card :=
    card_le_card (fun j hj => h j (mem_inter.mp hj).2 (mem_outN.mp (mem_inter.mp hj).1).2)
  by_cases tight : O.card=d
  · obtain ⟨pa,py,pw⟩ := parents x xv tight
    have le := bound (S:={q}) (by
      intro j hj e
      simp only [C,mem_insert,mem_singleton] at hj
      rcases hj with rfl|rfl|rfl|rfl
      · exact (out (by simp [C,pa e])).elim
      · simp
      · exact (out (by simp [C,py e])).elim
      · exact (out (by simp [C,pw e])).elim)
    rw [card_singleton] at le
    omega
  have pair (b c : ℕ) : ({b,c}:Finset ℕ).card≤2 := by
    have := card_insert_le b ({c}:Finset ℕ); simpa using this
  have loseTwo : (O ∩ C).card≤2 := by
    rcases split hx with qx | ⟨ny,nw⟩
    · have nq := digonfree free (by decide) hq xv qx
      have fail : ¬(D x a=true ∧ D x y=true ∧ D x w=true) := fun hits =>
        none ⟨x,hx,by change d<O.card; omega,qx,hits⟩
      by_cases ea : D x a=true
      · by_cases ey : D x y=true
        · apply (bound (S:={a,y}) ?_).trans (pair _ _)
          intro j hj e
          simp only [C,mem_insert,mem_singleton] at hj ⊢
          rcases hj with rfl|rfl|rfl|rfl <;> tauto
        · apply (bound (S:={a,w}) ?_).trans (pair _ _)
          intro j hj e
          simp only [C,mem_insert,mem_singleton] at hj ⊢
          rcases hj with rfl|rfl|rfl|rfl <;> tauto
      · apply (bound (S:={y,w}) ?_).trans (pair _ _)
        intro j hj e
        simp only [C,mem_insert,mem_singleton] at hj ⊢
        rcases hj with rfl|rfl|rfl|rfl <;> tauto
    · apply (bound (S:={a,q}) ?_).trans (pair _ _)
      intro j hj e
      simp only [C,mem_insert,mem_singleton] at hj ⊢
      rcases hj with rfl|rfl|rfl|rfl <;> tauto
  omega

#print axioms same_payers
#print axioms forced_triple_parent

/-- The checked one-sided contraction applies with either representative,
including when incoming arcs at the two original labels differ. -/
theorem pair_contraction {D : CH.Digraph} {V : Finset ℕ} {y w : ℕ}
    (free : QFree D V 3) (hy : y∈V) (hw : w∈V)
    (nested : outN D V w=(outN D V y).erase w) :
    ∀ k∈({y,w}:Finset ℕ), QFree (outContract D {y,w} k) (representativeSet V {y,w} k) 3 := by
  have same {j} (hj : j∈V) (jw : j≠w) : D w j=D y j := by
    apply Bool.eq_iff_iff.mpr
    have h := Finset.ext_iff.mp nested j
    simpa [mem_outN,hj,jw] using h
  intro k hk
  apply outContract_qfree free (insert_subset hy (singleton_subset_iff.mpr hw)) hk
  intro b hb c hc j hj outside
  have e := same hj (fun eq => outside (by simp [eq]))
  simp only [mem_insert,mem_singleton] at hb hc
  rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> first | rfl | exact e | exact e.symm

/-- Every exterior row loses precisely one head if it saw both labels, and
zero otherwise. This formula is symmetric in the two labels. -/
theorem contracted_row {D : CH.Digraph} {V : Finset ℕ} {x k r : ℕ}
    (hk : k∈V) (hr : r∈V) (kr : k≠r) (xk : x≠k) :
    (outN (outContract D {k,r} k) (representativeSet V {k,r} k) x).card +
      (if D x k=true ∧ D x r=true then 1 else 0) = (outN D V x).card := by
  classical
  let O := outN D V x
  have carrier : representativeSet V {k,r} k=V.erase r := by
    ext j
    by_cases a : j=k <;> by_cases b : j=r <;> simp_all [representativeSet]
  have row : outN (outContract D {k,r} k) (representativeSet V {k,r} k) x =
      if D x r=true then insert k (O.erase r) else O.erase r := by
    rw [carrier]
    ext j
    by_cases er : D x r=true <;> by_cases jk : j=k <;> by_cases jr : j=r <;>
      simp_all [outContract,mem_outN,O]
  rw [row]
  by_cases er : D x r=true
  · have hit : r∈O := mem_outN.mpr ⟨hr,er⟩
    simp only [er,ite_true]
    by_cases ek : D x k=true
    · have keep : k∈O.erase r := mem_erase.mpr ⟨kr,mem_outN.mpr ⟨hk,ek⟩⟩
      rw [insert_eq_of_mem keep,card_erase_of_mem hit]
      have := card_pos.mpr ⟨r,hit⟩
      simp only [ek,and_self,ite_true]
      change O.card-1+1=O.card
      omega
    · have fresh : k∉O.erase r := fun h => ek (mem_outN.mp (mem_of_mem_erase h)).2
      rw [card_insert_of_notMem fresh,card_erase_of_mem hit]
      have := card_pos.mpr ⟨r,hit⟩
      simp only [ek]
      change O.card-1+1=O.card
      omega
  · have miss : r∉O := fun h => er (mem_outN.mp h).2
    simp [er,erase_eq_of_notMem miss,O]

#print axioms pair_contraction
#print axioms contracted_row

/-- At the forced common parent, either the same row identity propagates
one step to q, or an actual full row is a common head of x,a,y,w and
points to both blockers. The two alternatives may be tested on one graph. -/
theorem upstream_alternative {D : CH.Digraph} {V : Finset ℕ} {d x q a y w u v : ℕ}
    (free : QFree D V 3) (size : V.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ z∈V, d≤(outN D V z).card) (hx : x∈V) (hq : q∈V)
    (ha : a∈V) (hy : y∈V) (hw : w∈V) (hu : u∈V) (hv : v∈V)
    (yw : D y w=true) (qx : D q x=true) (qa : D q a=true) (ay : D a y=true)
    (xy : D x y=true) (xw : D x w=true) (uq : D u q=true) (vq : D v q=true)
    (xdeg : (outN D V x).card=d+1) (qdeg : (outN D V q).card=d)
    (parentX : ∀ z∈V, (outN D V z).card=d → D z x=true → z=q)
    (parentA : ∀ z∈V, (outN D V z).card=d → D z a=true → z=q)
    (parentY : ∀ z∈V, (outN D V z).card=d → D z y=true → z=a)
    (parentQ : ∀ z∈V, (outN D V z).card=d → D z q=true → z=u ∨ z=v)
    (five : ∀ z∈V, (outN D V z).card=d → z=q ∨ z=a ∨ z=w ∨ z=u ∨ z=v)
    (dom : ∀ z∈V, ∃ p∈V, (outN D V p).card=d ∧ D p z=true)
    (nested : outN D V w=(outN D V y).erase w) (headsA : outN D V a⊆insert y (outN D V y)) :
    outN D V q=insert x (((outN D V x).erase y).erase w) ∨
    ∃ f∈V, d<(outN D V f).card ∧ D q f≠true ∧ D x f=true ∧ D a f=true ∧
      D y f=true ∧ D w f=true ∧ D f u=true ∧ D f v=true := by
  classical
  let S := ((outN D V x).erase y).erase w
  by_cases sub : S⊆outN D V q
  · left
    symm
    apply eq_of_subset_of_card_le (insert_subset (mem_outN.mpr ⟨hx,qx⟩) sub)
    have wy : w≠y := fun eq => loopfree free (by decide) hy (eq ▸ yw)
    have wy' : w∈(outN D V x).erase y := mem_erase.mpr ⟨wy,mem_outN.mpr ⟨hw,xw⟩⟩
    have fresh : x∉S := fun ht => loopfree free (by decide) hx
      (mem_outN.mp (mem_of_mem_erase (mem_of_mem_erase ht))).2
    change (outN D V q).card ≤ (insert x S).card
    rw [card_insert_of_notMem fresh,qdeg]
    dsimp only [S]
    rw [card_erase_of_mem wy',card_erase_of_mem (mem_outN.mpr ⟨hy,xy⟩),xdeg]
    omega
  · right
    obtain ⟨f,hit,miss⟩ := not_subset.mp sub
    have fw := (mem_erase.mp hit).1
    have fy := (mem_erase.mp (mem_of_mem_erase hit)).1
    have edge := mem_outN.mp (mem_of_mem_erase (mem_of_mem_erase hit))
    obtain ⟨fv,xf⟩ := edge
    have no : D q f≠true := fun e => miss (mem_outN.mpr ⟨fv,e⟩)
    have rich : d<(outN D V f).card := by
      by_contra! low
      rcases five f fv (le_antisymm low (degree f fv)) with rfl|rfl|rfl|rfl|rfl
      · exact digonfree free (by decide) hq hx qx xf
      · exact no qa
      · exact fw rfl
      · exact triangle free hq hx hu qx xf uq
      · exact triangle free hq hx hv qx xf vq
    obtain ⟨fu,fv'⟩ := reroot_full_head free size law degree hx hq fv qx xf parentX parentQ rich no
    have yh : f∈outN D V y := by
      obtain ⟨p,pin,pdeg,pf⟩ := dom f fv
      rcases five p pin pdeg with rfl|rfl|rfl|rfl|rfl
      · exact (no pf).elim
      · exact (mem_insert.mp (headsA (mem_outN.mpr ⟨fv,pf⟩))).resolve_left fy
      · exact mem_of_mem_erase (nested ▸ (mem_outN.mpr ⟨fv,pf⟩))
      · exact (digonfree free (by decide) fv hu fu pf).elim
      · exact (digonfree free (by decide) fv hv fv' pf).elim
    have yf := (mem_outN.mp yh).2
    have af := must_share free size law degree hy ha fv ay yf parentY parentA (.inl rich)
    have wh : f∈outN D V w := nested ▸ mem_erase.mpr ⟨fw,yh⟩
    exact ⟨f,fv,rich,no,xf,af,yf,(mem_outN.mp wh).2,fu,fv'⟩

#print axioms upstream_alternative
end LeanCH.BR.ShenPuncture.FiveParent
