import checkpoints.shen_extension.BlockSlack
import checkpoints.shen_extension.RecursivePackingFrontier

/-! Incoming block incidences, with nonuniform block sizes and an arbitrary
set of tested quotient rows. The local lower-degree law is required only on
the tested rows. -/
namespace LeanCH.BR.BlockSlack
open Finset BRq2 BRq3

variable {ι : Type*}

/-- Sum only rows in S, while retaining every target column in C. -/
theorem incoming_sum_on (adj : ι → ι → Prop) [DecidableRel adj]
    (w : ι → ℕ) (S C : Finset ι) :
    ∑ i∈S, inSum adj w C i = ∑ j∈C, (S.filter (fun i => adj i j)).card * w j := by
  unfold inSum
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter,sum_const,smul_eq_mul]

variable [Fintype ι] [DecidableEq ι] {D : CH.Digraph} {V : Finset ℕ}
    {blk : ℕ → ι} {adj : ι → ι → Prop} [DecidableRel adj] {q R : ℕ}

theorem selected_block_bound (S : Finset ι) (hF : Follows D V blk adj)
    (hirr : ∀ i, ¬adj i i) (free : QFree D V q) (degree : ∀ x∈V, R ≤ (outN D V x).card)
    (live : ∀ i∈S, (B V blk i).Nonempty)
    (law : ∀ i∈S, inSum adj (fun j => (B V blk j).card) univ i < R →
      Below q (R-inSum adj (fun j => (B V blk j).card) univ i)) :
    S.card*(q*R+1) ≤ (∑ i∈S, (B V blk i).card) +
      q*∑ j, (S.filter (fun i => adj i j)).card*(B V blk j).card := by
  let w := fun j => (B V blk j).card
  have per i (hi : i∈S) : q*R+1 ≤ w i+q*inSum adj w univ i := by
    have h := slack_nonneg_block hF hirr free degree i (live i hi) (law i hi)
    change 0 ≤ (w i : ℤ) - (q : ℤ)*((R : ℤ)-(inSum adj w univ i : ℤ))-1 at h
    exact_mod_cast (show (q : ℤ)*R+1 ≤ (w i : ℤ)+q*(inSum adj w univ i : ℤ) by linarith)
  have total := sum_le_sum per
  simpa only [sum_const,Nat.nsmul_eq_mul,sum_add_distrib,← mul_sum,
    incoming_sum_on] using total

theorem irregular_block_bound (hF : Follows D V blk adj) (hirr : ∀ i, ¬adj i i)
    (free : QFree D V q) (degree : ∀ x∈V, R ≤ (outN D V x).card)
    (live : ∀ i, (B V blk i).Nonempty)
    (law : ∀ i, inSum adj (fun j => (B V blk j).card) univ i < R →
      Below q (R-inSum adj (fun j => (B V blk j).card) univ i)) :
    Fintype.card ι*(q*R+1) ≤ V.card +
      q*∑ j, (univ.filter (fun i => adj i j)).card*(B V blk j).card := by
  simpa only [card_univ,← card_eq_sum_blocks V blk] using
    selected_block_bound univ hF hirr free degree (fun i _ => live i) (fun i _ => law i)

/-- For a selected cycle with only its cycle arcs inside, each selected label
has exactly one parent in S. At order at most qR, an outside block must
receive arcs from strictly more than |S|/q of those labels. -/
theorem outside_heavy_column (S : Finset ι) (wide : q+1≤S.card)
    (inside : ∀ j∈S, (S.filter (fun i => adj i j)).card≤1)
    (hF : Follows D V blk adj) (hirr : ∀ i, ¬adj i i)
    (free : QFree D V q) (degree : ∀ x∈V, R ≤ (outN D V x).card)
    (live : ∀ i∈S, (B V blk i).Nonempty)
    (law : ∀ i∈S, inSum adj (fun j => (B V blk j).card) univ i < R →
      Below q (R-inSum adj (fun j => (B V blk j).card) univ i)) (size : V.card≤q*R) :
    ∃ j∉S, S.card < q*(S.filter (fun i => adj i j)).card := by
  classical
  by_contra! outside
  let w := fun j => (B V blk j).card
  let c := fun j => (S.filter (fun i => adj i j)).card
  have fees (j : ι) : (if j∈S then w j else 0) + q*(c j*w j) ≤ S.card*w j := by
    by_cases h : j∈S
    · have le : 1+q*c j ≤ S.card := by
        have := Nat.mul_le_mul_left q (inside j h)
        dsimp [c]
        simp only [Nat.mul_one] at this
        omega
      simpa [h,add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (w j) le
    · simpa [h,Nat.mul_assoc] using Nat.mul_le_mul_right (w j) (outside j h)
  have bound := sum_le_sum (s:=univ) (fun j _ => fees j)
  rw [sum_add_distrib,← mul_sum,← mul_sum,← sum_filter] at bound
  have filt : univ.filter (fun j : ι => j∈S)=S := by ext; simp
  rw [filt] at bound
  have tot : ∑ j, w j=V.card := (card_eq_sum_blocks V blk).symm
  rw [tot] at bound
  have need := selected_block_bound S hF hirr free degree live law
  have no := need.trans bound
  exact (Nat.mul_lt_mul_of_pos_left (show V.card < q*R+1 by omega)
    (show 0<S.card by omega)).not_ge no

#print axioms irregular_block_bound
#print axioms outside_heavy_column
/-- On the native frontier the least order excludes a sink block and first
failure supplies every smaller-degree law needed by the selected rows. -/
theorem frontier_outside_column {d : ℕ} {O : Closure.Origin q (d+1)} {st : Closure.State}
    (fr : Closure.PackingFrontier.Frontier O st) (S : Finset ι) (hq : 1≤q)
    (wide : q+1≤S.card) (inside : ∀ j∈S, (S.filter (fun i => adj i j)).card≤1)
    (follows : Follows O.G O.V blk adj) (hirr : ∀ i, ¬adj i i)
    (live : ∀ i∈S, (B O.V blk i).Nonempty) :
    ∃ j∉S, S.card < q*(S.filter (fun i => adj i j)).card := by
  apply outside_heavy_column S wide inside follows hirr O.free O.deg live _ O.order
  intro i hi low
  let w := fun j => (B O.V blk j).card
  have positive : 0 < inSum adj w univ i := by
    by_contra! zero
    have inner (x) (hx : x∈B O.V blk i) : d+1≤(outN O.G (B O.V blk i) x).card := by
      obtain ⟨xV,xi⟩ := mem_filter.mp hx
      have eq := outdeg_split_irrefl follows hirr xV
      rw [xi] at eq
      change (outN O.G O.V x).card=(outN O.G (B O.V blk i) x).card+inSum adj w univ i at eq
      have := O.deg x xV
      omega
    have sz := O.least _ _ (block_free O.free i) inner (live i hi)
    have allBlock : B O.V blk i=O.V := eq_of_subset_of_card_le (filter_subset _ _) sz
    have second : ∃ j∈S, j≠i := by
      by_contra! none
      have sub : S⊆{i} := fun j hj => mem_singleton.mpr (none _ hj)
      have cc := card_le_card sub
      rw [card_singleton] at cc
      omega
    obtain ⟨j,hj,ne⟩ := second
    obtain ⟨x,hx⟩ := live j hj
    have hV := (mem_filter.mp hx).1
    have inI : x∈B O.V blk i := by rwa [allBlock]
    exact ne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp inI).2)
  change inSum adj w univ i<d+1 at low
  intro F K ne free deg
  exact fr.lower_degrees _ (by change d+1-inSum adj w univ i<d+1; omega) F K free deg ne

#print axioms frontier_outside_column
end LeanCH.BR.BlockSlack
