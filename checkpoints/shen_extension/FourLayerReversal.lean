import checkpoints.shen_extension.RotatedThreeRows

/-! Reversing a cut arc pays for the three deficits inside the complete four
layers. A remaining obstruction must charge an exterior vertex twice. -/

namespace LeanCH.BR.FourLayerReversal
open Finset BRq2 BRq3 BR45 JointFreeTargets TripleBank TwoRowShared

inductive Role | a | b | c | x | j | u | w | z
  deriving DecidableEq
open Role

instance : Fintype Role := ⟨{a,b,c,x,j,u,w,z},fun i => by cases i <;> simp⟩

local instance (p : Role → Prop) [DecidablePred p] : Decidable (∀ i, p i) := Fintype.decidableForallFintype

def shortRows : Finset Role := {a,b,c}
def middles : Finset Role := {x,j}
def targets : Finset Role := {u,w,z}

def gains : Role → Finset Role
  | .a => {u} | .b => {w} | .c => {z} | .x => {w} | _ => ∅

def cuts : Role → Finset Role
  | .u | .z => {j}
  | .w => {x}
  | .x => {a,c}
  | .j => {b}
  | _ => ∅

/-- Permitted old arcs on the eight labels. Among the three targets, w is
chosen to have no outgoing arc to the other two. The middle j misses x. -/
def allowed (i k : Role) : Bool := decide (i ≠ k ∧
  ((i ∈ shortRows ∧ k ∈ shortRows) ∨ (i ∈ middles ∧ k ∈ shortRows) ∨
   (i ∈ targets ∧ k ∈ middles) ∨ (i ∈ targets ∧ i ≠ w ∧ k ∈ targets) ∨
   (i = x ∧ k = j)))

private theorem shape :
    (∀ i, ∀ h ∈ gains i, h ≠ i ∧ allowed i h = false ∧
      (allowed h i = false ∨ i ∈ cuts h) ∧ gains h = ∅) ∧
    (∀ i, ∀ h ∈ gains i, ∀ m, allowed h m = true → allowed m i = true →
      m ∈ cuts h ∨ i ∈ cuts m) ∧
    (∀ i, if i ∈ shortRows then (cuts i).card + 1 ≤ (gains i).card
      else (cuts i).card ≤ 1 + (gains i).card) := by decide

/-- Distinct return legs that the exterior middle m must cut. The row b
and middle x both choose w, and are counted separately if m sees both. -/
def charges (D : CH.Digraph) (v : Role ↪ ℕ) (m : ℕ) : Finset Role :=
  univ.filter (fun i => D m (v i) = true ∧ ∃ h ∈ gains i, D (v h) m = true)

private noncomputable def liftRow (v : Role ↪ ℕ) (f : Role → Finset Role) (m : ℕ) : Finset ℕ := by
  classical
  exact if hm : ∃ i, v i = m then (f hm.choose).map v else ∅

@[simp] private theorem lift_at (v : Role ↪ ℕ) (f : Role → Finset Role) (i : Role) :
    liftRow v f (v i) = (f i).map v := by
  classical
  have hi : ∃ k, v k = v i := ⟨i,rfl⟩
  rw [liftRow,dite_eq_left hi,v.injective hi.choose_spec]

@[simp] private theorem lift_off {v : Role ↪ ℕ} {m : ℕ} (off : ∀ i, m ≠ v i)
    (f : Role → Finset Role) : liftRow v f m = ∅ := by
  classical
  exact dite_eq_right (by rintro ⟨i,hi⟩; exact off i hi.symm)

private theorem from_label {v : Role ↪ ℕ} {m h : ℕ} {f : Role → Finset Role}
    (hit : h ∈ liftRow v f m) : ∃ i k, m = v i ∧ h = v k ∧ k ∈ f i := by
  classical
  by_cases eq : ∃ i, v i = m
  · obtain ⟨i,rfl⟩ := eq
    rw [lift_at] at hit
    obtain ⟨k,km,rfl⟩ := mem_map.mp hit
    exact ⟨i,k,rfl,rfl,km⟩
  · rw [liftRow,dite_eq_right eq] at hit
    exact False.elim (notMem_empty _ hit)

/-- An edit of a residual graph. Only the eight labels are prescribed.
All internal returns are paid, while each exterior middle pays its own bill. -/
theorem repair {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : Role ↪ ℕ)
    (free : QFree D U 3) (inside : ∀ i, v i ∈ U)
    (internal : ∀ i k, D (v i) (v k) = true → allowed i k = true)
    (need : ∀ i ∈ shortRows, t ≤ (outN D U (v i)).card + 1)
    (spare : ∀ i ∉ shortRows, t+1 ≤ (outN D U (v i)).card)
    (pay : ∀ m ∈ U, (∀ i, m ≠ v i) → t + (charges D v m).card ≤ (outN D U m).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ i, ∀ h ∈ gains i, E (v i) (v h) = true) ∧
      ∀ m ∈ U, t ≤ (outN E U m).card := by
  classical
  let H : CH.Digraph := fun m n => decide (D m n = true ∧ n ∉ liftRow v cuts m)
  have kept {m n} (hit : H m n = true) : D m n = true ∧ n ∉ liftRow v cuts m :=
    of_decide_eq_true hit
  have safe : QFree H U 3 := SignatureRestoration.free_sub free (fun _ _ hit => (kept hit).1)
  have row (m) : outN H U m = outN D U m \ liftRow v cuts m := by ext n; simp [H,mem_outN]; tauto
  let C (m : ℕ) := if ∃ i, v i = m then ∅ else (charges D v m).map v
  have empty (i) : C (v i) = ∅ := ite_eq_left ⟨i,rfl⟩
  let A := liftRow v gains
  obtain ⟨ok,deg⟩ := patch_certificate (D:=H) (A:=A) (C:=C) safe
    (fun _ _ _ h => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      obtain ⟨ki,old,rev,_⟩ := shape.1 i k hk
      refine ⟨inside k,fun eq => ki (v.injective eq),fun e => ?_,fun e => ?_⟩
      · exact Bool.noConfusion (old.symm.trans (internal i k (kept e).1))
      · rcases rev with bad | cut
        · exact Bool.noConfusion (bad.symm.trans (internal k i (kept e).1))
        · exact (kept e).2 (by simp [cut]))
    (fun _ _ _ h m _ hm mi => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      by_cases tagged : ∃ l, v l = m
      · obtain ⟨l,rfl⟩ := tagged
        rcases shape.2.1 i k hk l (internal k l (kept hm).1) (internal l i (kept mi).1) with cut | cut
        · exact False.elim ((kept hm).2 (by simp [cut]))
        · exact False.elim ((kept mi).2 (by simp [cut]))
      · right
        have due : i ∈ charges D v m := mem_filter.mpr ⟨mem_univ _,(kept mi).1,k,hk,(kept hm).1⟩
        simp [C,tagged,due])
    (fun _ _ _ h _ next => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      simp [A,(shape.1 i k hk).2.2.2] at next)
  refine ⟨_,ok,fun i k hk => by simp [patch,A,hk],?_⟩
  intro m mu
  rw [deg m mu,row]
  by_cases tagged : ∃ i, v i = m
  · obtain ⟨i,rfl⟩ := tagged
    simp only [empty,sdiff_empty,A,lift_at,card_map]
    have bound := card_le_card_sdiff_add_card (s:=outN D U (v i)) (t:=(cuts i).map v)
    rw [card_map] at bound
    have cost := shape.2.2 i
    by_cases short : i ∈ shortRows
    · rw [ite_eq_left short] at cost
      have h := need i short
      omega
    · rw [ite_eq_right short] at cost
      have h := spare i short
      omega
  · have off : ∀ i, m ≠ v i := fun i e => tagged ⟨i,e.symm⟩
    simp only [lift_off off,sdiff_empty,A,card_empty,Nat.add_zero,C,ite_eq_right tagged]
    have bound := card_le_card_sdiff_add_card (s:=outN D U m) (t:=(charges D v m).map v)
    rw [card_map] at bound
    have budget := pay m mu off
    omega


private theorem forbidden : ∀ i k, allowed i k = false →
    i=k ∨ (i∈shortRows ∧ k∈middles) ∨ (i∈middles ∧ k∈targets) ∨
    (i∈shortRows ∧ k∈targets) ∨ (i∈targets ∧ k∈shortRows) ∨
    (i=j ∧ k=x) ∨ (i=w ∧ k∈targets) := by decide

/-- In a source with the complete four layers, every such choice of labels
forces a double charge outside all four layers. The witness is nonadjacent
to each bank label in both directions. -/
theorem exterior_obstruction {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (sink : ∀ i ∈ targets, D (v w) (v i) ≠ true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y) :
    ∃ m ∈ V, (∀ i, m ≠ v i) ∧
      D m p ≠ true ∧ D p m ≠ true ∧ D m y ≠ true ∧ D y m ≠ true ∧
      2 ≤ (charges D v m).card := by
  classical
  let B : Finset ℕ := {p,y}
  let U := V \ B
  let S := inN D V p ∩ inN D V y
  let R := S \ shortRows.map v
  have bv : B ⊆ V := insert_subset pv (singleton_subset_iff.mpr yv)
  have tri {l m n} (lv : l∈V) (mv : m∈V) (nv : n∈V)
      (lm : D l m=true) (mn : D m n=true) : D n l ≠ true := fun nl =>
    free l 3 (by decide) (by decide) (.step mv lm (.step nv mn (.step lv nl (.refl _))))
  have su {r} (rs : r∈S) : r∈U := by
    obtain ⟨rp,ry⟩ := mem_inter.mp rs
    obtain ⟨rv,rp⟩ := mem_inN.mp rp
    have np : r≠p := fun e => loopfree free (by decide) pv (e ▸ rp)
    have ny : r≠y := fun e => loopfree free (by decide) yv (e ▸ (mem_inN.mp ry).2)
    exact mem_sdiff.mpr ⟨rv,by simp [B,np,ny]⟩
  have short {i} (im : i∈shortRows) : v i ∈ S :=
    mem_inter.mpr ⟨mem_inN.mpr ⟨live i,(hit i im).1⟩,mem_inN.mpr ⟨live i,(hit i im).2⟩⟩
  have head {k} (km : k∈targets) : v k ∈ U ∧ v k ∉ S ∧ ∀ h ∈ B, D h (v k) = true := by
    obtain ⟨pk,yk⟩ := heads k km
    have np : v k ≠ p := fun e => loopfree free (by decide) pv (e ▸ pk)
    have ny : v k ≠ y := fun e => loopfree free (by decide) yv (e ▸ yk)
    refine ⟨mem_sdiff.mpr ⟨live k,by simp [B,np,ny]⟩,
      fun ks => digonfree free (by decide) pv (live k) pk (mem_inN.mp (mem_inter.mp ks).1).2,?_⟩
    intro h hb
    rcases mem_insert.mp hb with rfl | hb
    · exact pk
    · exact mem_singleton.mp hb ▸ yk
  have bankMiss {k m} (km : k∈targets) (mv : m∈V) (arc : D (v k) m=true) :
      D m p ≠ true ∧ D m y ≠ true :=
    ⟨tri pv (live k) mv (heads k km).1 arc,tri yv (live k) mv (heads k km).2 arc⟩
  have middle {i} (im : i∈middles) : v i ∈ U ∧ v i ∉ S := by
    have ua : u ∈ targets := by decide
    have ui := back u ua i im
    obtain ⟨pu,yu⟩ := heads u ua
    have np : v i ≠ p := fun e => digonfree free (by decide) pv (live u) pu (e ▸ ui)
    have ny : v i ≠ y := fun e => digonfree free (by decide) yv (live u) yu (e ▸ ui)
    exact ⟨mem_sdiff.mpr ⟨live i,by simp [B,np,ny]⟩,
      fun is' => (bankMiss ua (live i) ui).1 (mem_inN.mp (mem_inter.mp is').1).2⟩
  have parts : ∀ i, i∈shortRows ∨ i∈middles ∨ i∈targets := by decide
  have core (i) : v i∈U ∧ v i∉R := by
    rcases parts i with si | mi | hi
    · exact ⟨su (short si),fun r => (mem_sdiff.mp r).2 (mem_map.mpr ⟨i,si,rfl⟩)⟩
    · exact ⟨(middle mi).1,fun r => (middle mi).2 (mem_sdiff.mp r).1⟩
    · exact ⟨(head hi).1,fun r => (head hi).2.1 (mem_sdiff.mp r).1⟩
  have internal (i k) (ik : D (v i) (v k) = true) : allowed i k = true := by
    by_contra! off
    rcases forbidden i k (by simpa using off) with rfl | ⟨is',km⟩ | ⟨im,kh⟩ | ⟨is',kh⟩ |
        ⟨ih,ks⟩ | ⟨rfl,rfl⟩ | ⟨rfl,kh⟩
    · exact loopfree free (by decide) (live i) ik
    · exact digonfree free (by decide) (live i) (live k) ik (legs k km i is')
    · exact digonfree free (by decide) (live i) (live k) ik (back k kh i im)
    · exact tri (live k) (live x) (live i) (back k kh x (by decide)) (legs x (by decide) i is') ik
    · exact tri (live k) pv (live i) (hit k ks).1 (heads i ih).1 ik
    · exact orderX ik
    · exact sink k kh ik
  have exits (r) (rr : r∈R) := others r (mem_sdiff.mp rr).1 (mem_sdiff.mp rr).2
  let f (r : ℕ) := if rr : r∈R then (exits r rr).choose else p
  have chosen {r} (rr : r∈R) : FreeTarget D V r (f r) ∧ f r∉S := by
    simpa only [f,dite_eq_left rr] using (exits r rr).choose_spec
  let E := addTargets D R f
  obtain ⟨safe,deg⟩ := free_repair (f:=f) (free.mono_set (show U⊆V from sdiff_subset))
    (fun r rr => ⟨retained_target (mem_sdiff.mp rr).1 (chosen rr).1,
      fun e => (chosen rr).2 (mem_sdiff.mp e).1⟩)
  have unchanged {m n} (mr : m∉R) : E m n = true ↔ D m n = true := by simp [E,addTargets,mr]
  have gain (m) : (outN D U m).card ≤ (outN E U m).card := by rw [deg]; omega
  have base {m} (mu : m∈U) : t ≤ (outN D U m).card+1 := by simpa [U,B] using retained_floor reg (mem_sdiff.mp mu).1 py
  have rich {k} (kh : k∈targets) := bank_rich free reg bv (head kh).1 (head kh).2.2
  have floor {m} (mu : m∈U) (ext : ∀ i, m ≠ v i) : t ≤ (outN E U m).card := by
    by_cases ms : m∈S
    · have mr : m∈R := mem_sdiff.mpr ⟨ms,fun e => by obtain ⟨i,_,eq⟩ := mem_map.mp e; exact ext i eq.symm⟩
      change t ≤ (outN (addTargets D R f) U m).card
      rw [deg,ite_eq_left mr]
      exact base mu
    · apply le_trans _ (gain m)
      by_contra! low
      have sh : m∈ U.filter (fun k => (outN D U k).card < t+1-1) := mem_filter.mpr ⟨mu,by simpa using low⟩
      rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv yv py (by omega)] at sh
      exact ms (mem_inter.mpr ⟨(mem_inN.mp sh).1,mem_inN.mpr ⟨(mem_sdiff.mp mu).1,(mem_inN.mp sh).2⟩⟩)
  have menus : ∀ i, ∀ k ∈ gains i, k∈targets := by decide
  by_contra absent
  have pay (m) (mu : m∈U) (ext : ∀ i, m ≠ v i) : t+(charges E v m).card ≤ (outN E U m).card := by
    by_cases empty : charges E v m = ∅
    · simpa [empty] using floor mu ext
    obtain ⟨i,im⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨_,_,k,hk,km⟩ := mem_filter.mp im
    have arc := (unchanged (core k).2).mp km
    have mv := (mem_sdiff.mp mu).1
    obtain ⟨mp,my⟩ := bankMiss (menus i k hk) mv arc
    have mr : m∉R := fun rr => mp (mem_inN.mp (mem_inter.mp (mem_sdiff.mp rr).1).1).2
    have eq : charges E v m = charges D v m := by
      ext h
      simp only [charges,mem_filter,mem_univ,true_and,unchanged mr,unchanged (core _).2]
    have rg := ((rich (menus i k hk)).2 m mu arc).ge.trans (gain m)
    by_contra! deficit
    have two : 2 ≤ (charges D v m).card := by rw [eq] at deficit; omega
    have sa : ∃ r ∈ shortRows, r ∈ charges D v m := by
      by_contra! none
      have sub : charges D v m ⊆ {x} := by
        intro r rm
        obtain ⟨_,_,h,hr,_⟩ := mem_filter.mp rm
        have classified : ∀ i, ∀ k ∈ gains i, i ∈ shortRows ∨ i=x := by decide
        exact mem_singleton.mpr ((classified r h hr).resolve_left (fun rs => none r rs rm))
      have small := card_le_card sub
      simp at small
      omega
    obtain ⟨r,rs,rm⟩ := sa
    have leg := (mem_filter.mp rm).2.1
    exact absent ⟨m,mv,ext,mp,tri mv (live r) pv leg (hit r rs).1,my,
      tri mv (live r) yv leg (hit r rs).2,two⟩
  obtain ⟨G,ok,_,paid⟩ := repair v safe (fun i => (core i).1)
    (fun i k ed => internal i k ((unchanged (core i).2).mp ed))
    (fun i _ => (base (core i).1).trans (Nat.add_le_add_right (gain _) 1))
    (fun i ns => by
      rcases parts i with si | mi | hi
      · exact False.elim (ns si)
      · exact ((rich (show u∈targets by decide)).2 _ (core i).1 (back u (by decide) i mi)).ge.trans (gain _)
      · exact (rich hi).1.ge.trans (gain _)) pay
  have size : U.card ≤ 3*t := by
    rw [show U = V \ {p,y} from rfl,card_sdiff_of_subset bv,card_pair py,order]
    omega
  exact no G U ⟨v a,(core a).1⟩ size ok paid

#print axioms exterior_obstruction

/-- Apart from the original two common parents of a and b, a double charge
either detects a new common parent of c and another row, or an intermediate
on w→m→x that also points to one of the short rows. -/
theorem classify_charge {D : CH.Digraph} {v : Role ↪ ℕ} {m : ℕ}
    (two : 2 ≤ (charges D v m).card) (off : ¬(D m (v a)=true ∧ D m (v b)=true)) :
    (c ∈ charges D v m ∧ (a ∈ charges D v m ∨ b ∈ charges D v m)) ∨
    (D (v w) m=true ∧ D m (v x)=true ∧ ∃ i ∈ shortRows, i ∈ charges D v m) := by
  classical
  let M := charges D v m
  have head {i} (h : i∈M) := (mem_filter.mp h).2.1
  have dis : ¬(a∈M ∧ b∈M) := fun h => off ⟨head h.1,head h.2⟩
  have cover {i} (h : i∈M) : i=a ∨ i=b ∨ i=c ∨ i=x := by
    obtain ⟨_,_,k,km,_⟩ := mem_filter.mp h
    exact (show ∀ i, ∀ k ∈ gains i, i=a ∨ i=b ∨ i=c ∨ i=x by decide) i k km
  obtain ⟨r,rm,s,sm,rs⟩ := one_lt_card.mp two
  by_cases xm : x∈M
  · right
    obtain ⟨_,mx,k,kg,km⟩ := mem_filter.mp xm
    have kw : k=w := mem_singleton.mp kg
    refine ⟨kw ▸ km,mx,?_⟩
    have selected {i} (h : i∈M) (ix : i≠x) : ∃ i∈shortRows, i∈M := by
      rcases cover h with rfl | rfl | rfl | hx
      · exact ⟨a,by decide,h⟩
      · exact ⟨b,by decide,h⟩
      · exact ⟨c,by decide,h⟩
      · exact False.elim (ix hx)
    by_cases rx : r=x
    · exact selected sm (fun e => rs (rx.trans e.symm))
    · exact selected rm rx
  · left
    change c ∈ M ∧ (a ∈ M ∨ b ∈ M)
    rcases cover rm with rfl | rfl | rfl | rfl <;>
      rcases cover sm with rfl | rfl | rfl | rfl <;> tauto

private theorem sink_of_three {D : CH.Digraph} {V T : Finset ℕ}
    (free : QFree D V 3) (tv : T ⊆ V) (three : T.card=3) :
    ∃ h ∈ T, ∀ k ∈ T, D h k ≠ true := by
  classical
  obtain ⟨h,k,l,hk,hl,kl,eq⟩ := card_eq_three.mp three
  have hv := tv (show h ∈ T by simp [eq])
  have kv := tv (show k ∈ T by simp [eq])
  have lv := tv (show l ∈ T by simp [eq])
  have loopi {i} (iv : i∈V) := loopfree free (by decide) iv
  have dig {i j} (iv : i∈V) (jv : j∈V) (ed : D i j=true) := digonfree free (by decide) iv jv ed
  have tri {i j k} (iv : i∈V) (jv : j∈V) (kv : k∈V) (ij : D i j=true) (jk : D j k=true)
      (ki : D k i=true) : False :=
    free i 3 (by decide) (by decide) (.step jv ij (.step kv jk (.step iv ki (.refl _))))
  by_contra! fail
  have step {i} (ii : i∈T) : D i h=true ∨ D i k=true ∨ D i l=true := by
    obtain ⟨m,mt,im⟩ := fail i ii
    rw [eq] at mt
    simp only [mem_insert,mem_singleton] at mt
    rcases mt with rfl | rfl | rfl <;> tauto
  have sh := step (show h∈T by simp [eq])
  have sk := step (show k∈T by simp [eq])
  have sl := step (show l∈T by simp [eq])
  have := loopi hv
  have := loopi kv
  have := loopi lv
  have := dig hv kv
  have := dig hv lv
  have := dig kv lv
  have := tri hv kv lv
  have := tri hv lv kv
  tauto

/-- The original graph with bank p,y deleted still records both forbidden
directions. -/
def neutral (D : CH.Digraph) (p y m : ℕ) : Prop :=
  D m p ≠ true ∧ D p m ≠ true ∧ D m y ≠ true ∧ D y m ≠ true

private def replaceTargets (v : Role ↪ ℕ) (g : Role → ℕ)
    (inject : ∀ i∈targets, ∀ k∈targets, g i = g k → i=k)
    (away : ∀ i∈targets, ∀ k∉targets, g i ≠ v k) : Role ↪ ℕ where
  toFun i := if i∈targets then g i else v i
  inj' := by
    intro i k eq
    by_cases ih : i∈targets <;> by_cases kh : k∈targets <;> simp [ih,kh] at eq
    · exact inject i ih k kh eq
    · exact False.elim (away i ih k kh eq)
    · exact False.elim (away k kh i ih eq.symm)
    · exact eq

open scoped Classical

/-- Either a bank obtained by substituting c for a or b has an exterior third
common parent, or all but at most two original blockers have an exterior
two-step path to the same middle x, via a neutral vertex that hits a short row.
The x,j order is fixed before quantifying over the blocker set W. -/
theorem swap_or_returns {D : CH.Digraph} {V W : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i∉targets, v i∈V) (pv : p∈V) (yv : y∈V) (py : p≠y) (wv : W⊆V)
    (exactS : inN D V (v a) ∩ inN D V (v b) = {v x,v j})
    (hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true)
    (heads : ∀ h∈W, D p h=true ∧ D y h=true)
    (back : ∀ h∈W, ∀ i∈middles, D h (v i)=true)
    (legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true)
    (orderX : D (v j) (v x)≠true)
    (others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y) :
    (∃ m∈V, (∀ i∉targets, m ≠ v i) ∧ neutral D p y m ∧ D m (v c)=true ∧
      (D m (v a)=true ∨ D m (v b)=true)) ∨
    (W.filter (fun h => ¬∃ m∈V, (∀ i∉targets, m≠v i) ∧ neutral D p y m ∧
      D h m=true ∧ D m (v x)=true ∧ ∃ i∈shortRows, D m (v i)=true)).card ≤ 2 := by
  classical
  by_cases swap : ∃ m∈V, (∀ i∉targets, m≠v i) ∧ neutral D p y m ∧ D m (v c)=true ∧
      (D m (v a)=true ∨ D m (v b)=true)
  · exact Or.inl swap
  right
  let Bad := W.filter (fun h => ¬∃ m∈V, (∀ i∉targets, m≠v i) ∧ neutral D p y m ∧
      D h m=true ∧ D m (v x)=true ∧ ∃ i∈shortRows, D m (v i)=true)
  change Bad.card ≤ 2
  by_contra! big
  obtain ⟨T,tB,tc⟩ := exists_subset_card_eq (show 3 ≤ Bad.card by omega)
  have tW : T ⊆ W := tB.trans (filter_subset _ _)
  obtain ⟨d,dt,sink⟩ := sink_of_three free (tW.trans wv) tc
  obtain ⟨e,f,ef,rest⟩ := card_eq_two.mp (show (T.erase d).card=2 by rw [card_erase_of_mem dt,tc])
  have et : e ∈ T.erase d := by simp [rest]
  have ft : f ∈ T.erase d := by simp [rest]
  obtain ⟨ed,et⟩ := mem_erase.mp et
  obtain ⟨fd,ft⟩ := mem_erase.mp ft
  let g : Role → ℕ := fun i => if i=u then e else if i=w then d else f
  have inT {i} (ih : i∈targets) : g i∈T := by
    have opts : i=u ∨ i=w ∨ i=z := by simpa [targets] using ih
    rcases opts with rfl | rfl | rfl <;> simp_all [g]
  have inj : ∀ i∈targets, ∀ k∈targets, g i=g k → i=k := by
    intro i ih k kh eq
    simp only [targets,mem_insert,mem_singleton] at ih kh
    rcases ih with rfl | rfl | rfl <;> rcases kh with rfl | rfl | rfl <;>
      simp_all [g,Ne.symm]
  have part : ∀ i, i∉targets → i∈shortRows ∨ i∈middles := by decide
  have away : ∀ i∈targets, ∀ k∉targets, g i≠v k := by
    intro i ih k kh eq
    have gi := tW (inT ih)
    rcases part k kh with rs | mid
    · exact digonfree free (by decide) pv (live k kh) ((eq ▸ (heads _ gi).1) : D p (v k)=true) (hit k rs).1
    · exact loopfree free (by decide) (live k kh) (eq ▸ back _ gi k mid)
  let l := replaceTargets v g inj away
  have old {i} (non : i∉targets) : l i=v i := ite_eq_right non
  have new' {i} (ih : i∈targets) : l i=g i := ite_eq_left ih
  have rsOff : ∀ i∈shortRows, i∉targets := by decide
  have midOff : ∀ i∈middles, i∉targets := by decide
  have same : shortRows.map l = shortRows.map v := by
    ext n
    simp only [mem_map]
    constructor <;> rintro ⟨i,im,rfl⟩
    · exact ⟨i,im,(old (rsOff i im)).symm⟩
    · exact ⟨i,im,old (rsOff i im)⟩
  obtain ⟨m,mv,ext,mp,pm,my,ym,two⟩ := exterior_obstruction l free reg ht order no
    (fun i => by by_cases ih : i∈targets
                 · rw [new' ih]; exact wv (tW (inT ih))
                 · rw [old ih]; exact live i ih)
    pv yv py
    (fun i rs => by rw [old (rsOff i rs)]; exact hit i rs)
    (fun i ih => by rw [new' ih]; exact heads _ (tW (inT ih)))
    (fun k kh i im => by rw [new' kh,old (midOff i im)]; exact back _ (tW (inT kh)) i im)
    (fun i im k ks => by rw [old (midOff i im),old (rsOff k ks)]; exact legs i im k ks)
    (by simpa only [old (by decide : j∉targets),old (by decide : x∉targets)] using orderX)
    (fun i ih => by rw [new' (by decide : w∈targets),new' ih]; exact sink _ (inT ih))
    (fun r rh off => others r rh (same ▸ off))
  have exterior (i) (ih : i∉targets) : m≠v i := by simpa only [old ih] using ext i
  have neu : neutral D p y m := ⟨mp,pm,my,ym⟩
  have off : ¬(D m (l a)=true ∧ D m (l b)=true) := by
    rintro ⟨ma,mb⟩
    rw [old (by decide : a∉targets)] at ma
    rw [old (by decide : b∉targets)] at mb
    have pred : m ∈ inN D V (v a) ∩ inN D V (v b) := mem_inter.mpr
      ⟨mem_inN.mpr ⟨mv,ma⟩,mem_inN.mpr ⟨mv,mb⟩⟩
    rw [exactS] at pred
    simp [exterior x (by decide),exterior j (by decide)] at pred
  have sees {i} (ih : i∈charges D l m) (it : i∉targets) : D m (v i)=true := by
    simpa only [old it] using (mem_filter.mp ih).2.1
  rcases classify_charge two off with ⟨cm,ab⟩ | ⟨wm,mx,i,rs,im⟩
  · exact swap ⟨m,mv,exterior,neu,sees cm (by decide),ab.imp
      (fun am => sees am (by decide)) (fun bm => sees bm (by decide))⟩
  · have dh := (mem_filter.mp (tB dt)).2
    apply dh
    refine ⟨m,mv,exterior,neu,?_,?_,i,rs,sees im (rsOff i rs)⟩
    · simpa [new' (by decide : w∈targets),g] using wm
    · simpa only [old (by decide : x∉targets)] using mx

#print axioms classify_charge
#print axioms swap_or_returns

#print axioms repair
end LeanCH.BR.FourLayerReversal
