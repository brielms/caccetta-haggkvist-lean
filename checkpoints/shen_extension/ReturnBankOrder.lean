import checkpoints.shen_extension.SeparatedReturnBank
import checkpoints.shen_extension.RemoteBankDeletion

namespace LeanCH.BR.Closure.ReturnBankOrder
open Finset BRq2 BRq3 DeficitLevels

def shortRows (D : CH.Digraph) (W : Finset ℕ) (d : ℕ) :=
  W.filter (fun x => (outN D W x).card<d)

noncomputable def exits (D : CH.Digraph) (W : Finset ℕ) (q d : ℕ) : Finset ℕ := by
  classical
  exact W.filter (fun h => ∀i∈shortRows D W d, ∀k, k+2≤q → ¬Walk D W h i k)

/-- Every retained set has a canonical entrance and exit set, so the
test has no choice of intermediaries or common neighbors. -/
private theorem order_of {q s} (O : Origin q s) (hq : 1≤q)
    {W : Finset ℕ} {m d : ℕ} (wv : W⊆O.V)
    (budget : (d=s ∧ W.card+m<O.V.card) ∨ (OrderLaw q d (q*d+1) ∧ W.card+m≤q*d))
    (cap : ∀x∈W, d≤(outN O.G W x).card+m) :
    m≤q*(d-(exits O.G W q d).card) := by
  classical
  by_contra! room
  have hw : exits O.G W q d⊆W := filter_subset _ _
  have far (h) (hh : h∈exits O.G W q d) := (mem_filter.mp hh).2
  have pay (x) (hx : x∈W) : d≤(outN O.G W x).card+(if x∈shortRows O.G W d then m else 0) := by
    split_ifs with hit
    · exact cap x hx
    · have ge : d≤(outN O.G W x).card := by
        by_contra! lt
        exact hit (mem_filter.mpr ⟨hx,lt⟩)
      simpa using ge
  obtain ⟨E,U,live,uc,safe,deg⟩ := SeparatedReturnBank.funded (O.free.mono_set wv) hq hw far room pay
  rcases budget with ⟨rfl,small⟩|⟨below,small⟩
  · have le := O.least E U safe deg live
    omega
  · have le := below E U safe deg live
    omega

theorem same_order {q s} (O : Origin q s) (hq : 1≤q) {W : Finset ℕ} {m : ℕ}
    (wv : W⊆O.V) (budget : W.card+m<O.V.card)
    (cap : ∀x∈W, s≤(outN O.G W x).card+m) :
    m≤q*(s-(exits O.G W q s).card) :=
  order_of O hq wv (Or.inl ⟨rfl,budget⟩) cap

theorem order {q s} (O : Origin q s) (hq : 1≤q) (laws : ∀j<s, OrderLaw q j (q*j+1))
    {W : Finset ℕ} {m d : ℕ} (wv : W⊆O.V)
    (budget : (d=s ∧ W.card+m<O.V.card) ∨ (d<s ∧ W.card+m≤q*d))
    (cap : ∀x∈W, d≤(outN O.G W x).card+m) :
    m≤q*(d-(exits O.G W q d).card) :=
  order_of O hq wv (budget.imp_right fun ⟨low,b⟩ => ⟨laws d low,b⟩) cap

/-- For all cutoffs, at lower degree d a retained set of size at most
(q-1)d can have at most a 1/q share of exits beyond the short rows. -/
theorem exit_share {q s} (O : Origin q s) (hq : 1≤q) (laws : ∀j<s, OrderLaw q j (q*j+1))
    {W : Finset ℕ} {d : ℕ} (wv : W⊆O.V) (below : d<s) (pos : 0<d)
    (small : W.card+d≤q*d) : q*(exits O.G W q d).card≤W.card := by
  let m := q*d-W.card
  have eq : W.card+m=q*d := by dsimp [m]; omega
  have dm : d≤m := by omega
  have test := order O hq laws wv (Or.inr ⟨below,eq.le⟩) (fun x _ => by
    exact dm.trans (Nat.le_add_left _ _))
  have le : (exits O.G W q d).card≤d := by
    by_contra! big
    have zero : d-(exits O.G W q d).card=0 := by omega
    rw [zero,Nat.mul_zero] at test
    omega
  rw [Nat.mul_sub] at test
  have mul := Nat.mul_le_mul_left q le
  omega

/-- At q=3 the exit test is the zero/one-step condition on actual arcs. -/
theorem triangle_exits {D W d h} :
    h∈exits D W 3 d ↔ h∈W ∧ d≤(outN D W h).card ∧
      ∀i∈outN D W h, d≤(outN D W i).card := by
  classical
  constructor
  · intro hh
    obtain ⟨hw,far⟩ := mem_filter.mp hh
    refine ⟨hw,?_,?_⟩
    · by_contra! bad
      exact far h (mem_filter.mpr ⟨hw,bad⟩) 0 (by decide) (.refl _)
    · intro i hi
      by_contra! bad
      exact far i (mem_filter.mpr ⟨(mem_outN.mp hi).1,bad⟩) 1 (by decide)
        (.step (mem_outN.mp hi).1 (mem_outN.mp hi).2 (.refl _))
  · rintro ⟨hw,paid,each⟩
    refine mem_filter.mpr ⟨hw,?_⟩
    intro i hi k small path
    have low := (mem_filter.mp hi).2
    have kcases : k=0 ∨ k=1 := by omega
    rcases kcases with rfl|rfl
    · cases path; omega
    · cases path with
      | step iw arc tail =>
        cases tail
        exact (each _ (mem_outN.mpr ⟨iw,arc⟩)).not_gt low

#print axioms same_order
#print axioms order
#print axioms exit_share
#print axioms triangle_exits
end LeanCH.BR.Closure.ReturnBankOrder
