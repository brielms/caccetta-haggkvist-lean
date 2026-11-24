import checkpoints.shen_extension.WeightedSplitInduction
import LeanCH.BR.BRWeightedExtremalCompetitors

namespace LeanCH.BR.Closure.PunctureDualExtension
open Finset WeightedSD

/-- Capacities after eliminating one row weight. Columns of non-heads can
exceed their retained budget if every head has room to cover the excess. -/
def PairBudget (q : ℕ) (D : CH.Digraph) (W : Finset ℕ) (h : ℕ) (y : ℕ→ℚ) : Prop :=
  q*inW D W y h ≤ mass W y ∧
  (∀a∈W,D h a=true → col q D W y a ≤ mass W y) ∧
  ∀a∈W,D h a=true → ∀b∈W,D h b=false →
    col q D W y a + (q-1:ℚ)*col q D W y b ≤ q*mass W y

private theorem interval {q D W h y} (hq : 2≤q) :
    PairBudget q D W h y ↔
    q*inW D W y h≤mass W y ∧ ∃t:ℚ, 0≤t ∧
      ∀z∈W, col q D W y z+(if D h z=true then (q:ℚ)*t else 0)≤mass W y+t := by
  classical
  have qp : (0:ℚ)≤q-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤q by omega))
  constructor
  · rintro ⟨parents,heads,pairs⟩
    let debts := insert 0 ((W.filter (fun z => D h z=false)).image (fun z => col q D W y z-mass W y))
    let t := debts.max' ⟨0,mem_insert_self _ _⟩
    have top (x) (hx : x∈debts) : x≤t := le_max' _ _ hx
    refine ⟨parents,t,top 0 (mem_insert_self _ _),?_⟩
    intro z zw
    cases e : D h z with
    | false =>
      have b := top _ (mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨zw,e⟩)))
      simp; linarith
    | true =>
      have hit : t∈debts := max'_mem _ _
      rcases mem_insert.mp hit with zero | ex
      · have head := heads z zw e
        simp [zero,head]
      · obtain ⟨b,bmem,eq⟩ := mem_image.mp ex
        obtain ⟨bw,be⟩ := mem_filter.mp bmem
        have pair := pairs z zw e b bw be
        simp only [ite_true]
        rw [←eq]
        linarith
  · rintro ⟨parents,t,tn,pay⟩
    refine ⟨parents,?_,?_⟩
    · intro a aw ha
      have hi := pay a aw
      simp [ha] at hi
      nlinarith [mul_nonneg qp tn]
    · intro a aw ha b bw hb
      have hi := pay a aw
      have lo := pay b bw
      simp [ha] at hi
      simp [hb] at lo
      nlinarith [mul_nonneg qp (sub_nonneg.mpr lo)]

/-- The pair conditions are necessary and sufficient for extending these
specific retained multipliers by a nonnegative multiplier at h. -/
theorem iff_extend {q D W h y} (hq : 2≤q) (away : h∉W) (loop : D h h=false) :
    PairBudget q D W h y ↔ ∃t:ℚ, 0≤t ∧
      let p := fun x => if x=h then t else y x
      ∀z∈insert h W,col q D (insert h W) p z≤mass (insert h W) p := by
  classical
  rw [interval hq]
  have eqs (t : ℚ) :
      let p := fun x => if x=h then t else y x
      mass (insert h W) p=t+mass W y ∧
      col q D (insert h W) p h=t+q*inW D W y h ∧
      ∀z∈W, col q D (insert h W) p z=col q D W y z+(if D h z=true then (q:ℚ)*t else 0) := by
    intro p
    have eq (x) (xw : x∈W) : p x=y x := by simp [p,show x≠h from fun e => away (e ▸ xw)]
    have ys := sum_congr (s₁:=W) rfl eq
    have ins (z) : (∑x∈W,if D x z=true then p x else 0)=inW D W y z :=
      sum_congr rfl (fun x xw => by rw [eq x xw])
    have ph : p h=t := by simp [p]
    refine ⟨by simp only [mass,sum_insert away,ph,ys],?_,?_⟩
    · simp only [col,inW,sum_insert away,loop,Bool.false_eq_true,ite_false,zero_add,ph,ins]
    · intro z zw
      simp only [col,inW,sum_insert away,ph,ins,eq z zw]
      split_ifs <;> ring
  constructor
  · rintro ⟨pc,t,tn,rows⟩
    obtain ⟨sz,root,other⟩ := eqs t
    refine ⟨t,tn,?_⟩
    dsimp only
    intro z zh
    rw [sz]
    rcases mem_insert.mp zh with rfl | zw
    · rw [root]; linarith
    · rw [other z zw,add_comm t (mass W y)]; exact rows z zw
  · rintro ⟨t,tn,rows⟩
    obtain ⟨sz,root,other⟩ := eqs t
    have pr := rows h (mem_insert_self _ _)
    rw [sz,root] at pr
    refine ⟨by linarith,t,tn,?_⟩
    intro z zw
    have pz := rows z (mem_insert_of_mem zw)
    rwa [sz,other z zw,add_comm t (mass W y)] at pz

/-- A nonzero admissible retained assignment contradicts strict rows on
the original graph, including the nonparents of the removed vertex. -/
theorem excludes {q D W h y} (hq : 2≤q) (away : h∉W) (loop : D h h=false)
    (yn : ∀x∈W,0≤y x) (pos : ∃x∈W,0<y x) (pay : PairBudget q D W h y)
    (w : ℕ→ℚ) (wn : ∀x∈insert h W,0≤w x) :
    ¬(∀x∈insert h W,mass (insert h W) w<WeightedSD.row q D (insert h W) w x) := by
  classical
  obtain ⟨t,tn,fair⟩ := (iff_extend hq away loop).mp pay
  let V := insert h W
  let p := fun x => if x=h then t else y x
  have pn (x) (xv : x∈V) : 0≤p x := by
    rcases mem_insert.mp xv with rfl | xw
    · simpa [p] using tn
    · simpa [p,show x≠h from fun e => away (e ▸ xw)] using yn x xw
  obtain ⟨a,aw,ap⟩ := pos
  have pa : 0<p a := by simpa [p,show a≠h from fun e => away (e ▸ aw)] using ap
  intro high
  have lo := sum_lt_sum (s:=V) (f:=fun i => p i*mass V w) (g:=fun i => p i*WeightedSD.row q D V w i)
    (fun x xv => mul_le_mul_of_nonneg_left (high x xv).le (pn x xv))
    ⟨a,mem_insert_of_mem aw,mul_lt_mul_of_pos_left (high a (mem_insert_of_mem aw)) pa⟩
  rw [←sum_mul,rational_cross_rows] at lo
  have hi := sum_le_sum (s:=V) (fun x hx => mul_le_mul_of_nonneg_left (fair x hx) (wn x hx))
  rw [←sum_mul] at hi
  change mass V p*mass V w < _ at lo
  change _ ≤ mass V w*mass V p at hi
  rw [mul_comm (mass V w)] at hi
  exact lo.not_ge hi

#print axioms iff_extend
#print axioms excludes
end LeanCH.BR.Closure.PunctureDualExtension
