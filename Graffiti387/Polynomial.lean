import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.Minimal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Push

/-!
# The polynomial circuit lemma used for Graffiti.pc Conjecture 387

This file contains the linear-algebraic part of the proof.  Polynomials of
degree at most `d` are represented by their first `d + 1` coefficients.
-/

namespace Graffiti387

open scoped BigOperators Polynomial
open Finset Polynomial

noncomputable section

/-- The first `d + 1` coefficients of a polynomial. -/
def coeffVector (d : ℕ) (p : ℚ[X]) : Fin (d + 1) → ℚ :=
  fun j ↦ p.coeff j

/-- On polynomials of degree at most `d`, taking the first `d + 1`
coefficients preserves linear independence. -/
lemma linearIndependent_coeffVector {ι : Type*} [Finite ι]
    (d : ℕ) (p : ι → ℚ[X]) (hdeg : ∀ i, (p i).natDegree ≤ d)
    (hli : LinearIndependent ℚ p) :
    LinearIndependent ℚ (fun i ↦ coeffVector d (p i)) := by
  classical
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  apply (Fintype.linearIndependent_iff.mp hli c) ?_ i
  ext n
  by_cases hn : n < d + 1
  · have hcoord := congrFun hc ⟨n, hn⟩
    simpa [coeffVector] using hcoord
  · have hdn : d < n := by omega
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
      smul_eq_mul, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [(p j).coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_lt hdn), mul_zero]

/-- The monic polynomial whose roots are the labels of the elements of `A`. -/
def rootPolynomial {β : Type*} (a : β → ℚ) (A : Finset β) : ℚ[X] :=
  ∏ z ∈ A, (Polynomial.X - Polynomial.C (a z))

@[simp]
lemma natDegree_rootPolynomial {β : Type*} (a : β → ℚ) (A : Finset β) :
    (rootPolynomial a A).natDegree = A.card := by
  classical
  simp [rootPolynomial, Polynomial.natDegree_prod,
    Polynomial.X_sub_C_ne_zero]

lemma rootPolynomial_ne_zero {β : Type*} (a : β → ℚ) (A : Finset β) :
    rootPolynomial a A ≠ 0 := by
  classical
  rw [rootPolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact Polynomial.X_sub_C_ne_zero (a z)

lemma eval_rootPolynomial_eq_zero_of_mem {β : Type*}
    (a : β → ℚ) {A : Finset β} {z : β} (hz : z ∈ A) :
    Polynomial.eval (a z) (rootPolynomial a A) = 0 := by
  classical
  rw [rootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hz
  simp

lemma eval_rootPolynomial_ne_zero_of_not_mem {β : Type*}
    (a : β → ℚ) (ha : Function.Injective a) {A : Finset β} {z : β} (hz : z ∉ A) :
    Polynomial.eval (a z) (rootPolynomial a A) ≠ 0 := by
  classical
  rw [rootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
  exact fun h ↦ hz (ha h ▸ hy)

/-- A finite indexed family is minimally dependent if it is dependent but
becomes independent after any one index is removed. -/
def MinimallyDependent {ι : Type*} [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module ℚ M] (v : ι → M) : Prop :=
  ¬ LinearIndependent ℚ v ∧
    ∀ i, LinearIndependent ℚ (fun j : {j : ι // j ≠ i} ↦ v j)

set_option maxHeartbeats 800000 in
-- Finite-support elimination below expands a dependent-family relation.
/-- Every coefficient in a nontrivial relation on a minimally dependent
family is nonzero. -/
lemma MinimallyDependent.exists_relation_all_ne_zero
    {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℚ M]
    {v : ι → M} (hmin : MinimallyDependent v) :
    ∃ c : ι → ℚ, (∑ i, c i • v i = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  rcases hmin with ⟨hdep, hremove⟩
  obtain ⟨c, hsum, ⟨w, hw⟩⟩ :=
    (Fintype.not_linearIndependent_iff (R := ℚ) (v := v)).mp hdep
  refine ⟨c, hsum, fun i hci ↦ ?_⟩
  have hsumErase : ∑ j ∈ (Finset.univ.erase i), c j • v j = 0 := by
    have h := Finset.sum_erase_add Finset.univ (fun j ↦ c j • v j)
      (Finset.mem_univ i)
    rw [hsum, hci, zero_smul, add_zero] at h
    exact h
  have hsumSubtype : ∑ j : {j : ι // j ≠ i}, c j • v j = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp)
      (fun j ↦ c j • v j)]
    exact hsumErase
  have hzero := Fintype.linearIndependent_iff.mp (hremove i)
    (fun j : {j : ι // j ≠ i} ↦ c j) hsumSubtype
  apply hw
  by_cases hwi : w = i
  · simpa [hwi] using hci
  · exact hzero ⟨w, hwi⟩

/-- In a minimally dependent family of equal-degree root polynomials, an
element that is missing from one root set is missing from at least two. -/
lemma exists_second_not_mem_of_minimallyDependent
    {ι β : Type*} [Fintype ι]
    (a : β → ℚ) (ha : Function.Injective a) (A : ι → Finset β)
    (hmin : MinimallyDependent (fun i ↦ rootPolynomial a (A i)))
    {z : β} {j : ι} (hzj : z ∉ A j) :
    ∃ i, i ≠ j ∧ z ∉ A i := by
  classical
  by_contra h
  push Not at h
  obtain ⟨c, hsum, hc⟩ := hmin.exists_relation_all_ne_zero
  have heval := congrArg (Polynomial.eval (a z)) hsum
  simp only [Polynomial.eval_finsetSum, eval_smul, smul_eq_mul,
    Polynomial.eval_zero] at heval
  have hothers :
      ∑ i ∈ (Finset.univ.erase j),
        c i * Polynomial.eval (a z) (rootPolynomial a (A i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by simpa using hi
    rw [eval_rootPolynomial_eq_zero_of_mem a (h i hij), mul_zero]
  rw [← Finset.sum_erase_add Finset.univ
    (fun i ↦ c i * Polynomial.eval (a z) (rootPolynomial a (A i)))
    (Finset.mem_univ j), hothers, zero_add] at heval
  exact (mul_ne_zero (hc j) (eval_rootPolynomial_ne_zero_of_not_mem a ha hzj)) heval

/-- A nonzero common polynomial factor can be cancelled from a minimally
dependent family. -/
lemma MinimallyDependent.cancel_left_factor
    {ι : Type*} [Fintype ι] (g : ℚ[X]) (q : ι → ℚ[X]) (hg : g ≠ 0)
    (hmin : MinimallyDependent (fun i ↦ g * q i)) :
    MinimallyDependent q := by
  let L : ℚ[X] →ₗ[ℚ] ℚ[X] := LinearMap.mulLeft ℚ g
  have hL : Function.Injective L := by
    intro x y hxy
    apply mul_left_cancel₀ hg
    exact hxy
  constructor
  · intro hq
    have hmapped := hq.map' L (LinearMap.ker_eq_bot.mpr hL)
    apply hmin.1
    simpa [L, Function.comp_def] using hmapped
  · intro i
    apply LinearIndependent.of_comp L
    simpa [L, Function.comp_def] using hmin.2 i

/-- A minimally dependent family of polynomials of degree at most `d` has at
most `d + 2` members. -/
lemma MinimallyDependent.card_le_degree_add_two
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℚ[X]) (d : ℕ)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (hmin : MinimallyDependent p) :
    Fintype.card ι ≤ d + 2 := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hli := hmin.2 i₀
  have hcoeff : LinearIndependent ℚ
      (fun j : {j : ι // j ≠ i₀} ↦ coeffVector d (p j)) :=
    linearIndependent_coeffVector d (fun j : {j : ι // j ≠ i₀} ↦ p j)
      (fun j ↦ hdeg j) hli
  have hcard := hcoeff.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  have herase : Fintype.card {j : ι // j ≠ i₀} = Fintype.card ι - 1 := by
    simp [Fintype.card_subtype_compl]
  omega

/-- The elements occurring in every member of a finite indexed family. -/
def commonRoots {ι β : Type*} [Fintype ι] [Fintype β]
    (A : ι → Finset β) : Finset β := by
  classical
  exact Finset.univ.filter fun z ↦ ∀ i, z ∈ A i

lemma commonRoots_subset {ι β : Type*} [Fintype ι] [Fintype β]
    (A : ι → Finset β) (i : ι) : commonRoots A ⊆ A i := by
  classical
  intro z hz
  exact (Finset.mem_filter.mp (show z ∈ Finset.univ.filter
    (fun z ↦ ∀ i, z ∈ A i) from hz)).2 i

lemma rootPolynomial_common_mul_sdiff {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β]
    (a : β → ℚ) (A : ι → Finset β) (i : ι) :
    rootPolynomial a (commonRoots A) * rootPolynomial a (A i \ commonRoots A) =
      rootPolynomial a (A i) := by
  classical
  change
    (∏ z ∈ commonRoots A, (Polynomial.X - Polynomial.C (a z))) *
      (∏ z ∈ A i \ commonRoots A, (Polynomial.X - Polynomial.C (a z))) =
        ∏ z ∈ A i, (Polynomial.X - Polynomial.C (a z))
  rw [mul_comm]
  exact Finset.prod_sdiff (f := fun z ↦ Polynomial.X - Polynomial.C (a z))
    (commonRoots_subset A i)

/-- The intersection of the root sets in a minimally dependent equal-degree
family has the sharp circuit-size bound used in the graph proof. -/
lemma commonRoots_card_le
    {ι β : Type*} [Fintype ι] [Nonempty ι] [Fintype β]
    (a : β → ℚ) (A : ι → Finset β) (t : ℕ)
    (hcard : ∀ i, (A i).card = t)
    (hmin : MinimallyDependent (fun i ↦ rootPolynomial a (A i))) :
    (commonRoots A).card ≤ t + 2 - Fintype.card ι := by
  classical
  let P := commonRoots A
  let g := rootPolynomial a P
  let q : ι → ℚ[X] := fun i ↦ rootPolynomial a (A i \ P)
  have hfactor : (fun i ↦ rootPolynomial a (A i)) = fun i ↦ g * q i := by
    funext i
    exact (rootPolynomial_common_mul_sdiff a A i).symm
  have hg : g ≠ 0 := rootPolynomial_ne_zero a P
  have hmin' : MinimallyDependent q := by
    rw [hfactor] at hmin
    exact hmin.cancel_left_factor g q hg
  have hPsubset : ∀ i, P ⊆ A i := fun i ↦ commonRoots_subset A i
  have hPcard : P.card ≤ t := by
    simpa [hcard (Classical.choice inferInstance)] using
      Finset.card_le_card (hPsubset (Classical.choice inferInstance))
  have hqdeg : ∀ i, (q i).natDegree ≤ t - P.card := by
    intro i
    change (rootPolynomial a (A i \ P)).natDegree ≤ t - P.card
    rw [natDegree_rootPolynomial, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (hPsubset i), hcard i]
  have hbound := hmin'.card_le_degree_add_two q (t - P.card) hqdeg
  dsimp [P] at hPcard hbound ⊢
  omega

/-- Every finite dependent family of nonzero vectors contains a minimally
dependent indexed subfamily with at least two members. -/
lemma exists_minimallyDependent_finset
    {ι M : Type*} [Finite ι] [AddCommGroup M] [Module ℚ M]
    (v : ι → M) (hnz : ∀ i, v i ≠ 0) (hdep : ¬ LinearIndependent ℚ v) :
    ∃ C : Finset ι, 2 ≤ C.card ∧
      MinimallyDependent (fun i : C ↦ v i) := by
  classical
  letI := Fintype.ofFinite ι
  let Dep : Finset ι → Prop := fun C ↦
    ¬ LinearIndependent ℚ (fun i : C ↦ v i)
  have hDep : ∃ C, Dep C := by
    refine ⟨Finset.univ, ?_⟩
    intro hu
    let e : ι ≃ {x : ι // x ∈ (Finset.univ : Finset ι)} :=
      { toFun := fun x ↦ ⟨x, Finset.mem_univ x⟩
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    apply hdep
    have he := (linearIndependent_equiv e).2 hu
    simpa [e, Function.comp_def] using he
  obtain ⟨C, hC⟩ := exists_minimal_of_wellFoundedLT Dep hDep
  have hremove : ∀ i : C,
      LinearIndependent ℚ (fun j : {j : C // j ≠ i} ↦ v j) := by
    intro i
    let D := C.erase i
    have hD : LinearIndependent ℚ (fun j : D ↦ v j) := by
      by_contra hnot
      have hCD : C ⊆ D := hC.2 hnot (Finset.erase_subset i.val C)
      exact (Finset.notMem_erase i.val C) (hCD i.property)
    let e : {j : C // j ≠ i} ≃ D :=
      { toFun := fun j ↦ ⟨j, Finset.mem_erase.mpr ⟨by
            intro hji
            exact j.property (Subtype.ext hji), j.val.property⟩⟩
        invFun := fun j ↦ ⟨⟨j, (Finset.mem_of_mem_erase j.property)⟩, by
            intro hji
            exact (Finset.ne_of_mem_erase j.property)
              (congrArg (fun x : C ↦ (x : ι)) hji)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have he := hD.comp e e.injective
    simpa [e, D, Function.comp_def] using he
  refine ⟨C, ?_, hC.1, hremove⟩
  by_contra hcard
  have hcard' : C.card ≤ 1 := by omega
  letI : Subsingleton C := Fintype.card_le_one_iff_subsingleton.mp (by simpa using hcard')
  apply hC.1
  exact (linearIndependent_subsingleton_index_iff (fun i : C ↦ v i)).2
    (fun i ↦ hnz i)

/-- Polynomial-circuit selection lemma in the exact form needed by the graph
argument.  It produces a set of row indices `C` and a set of columns `Y` of
total size `t + 2`, while every column outside `Y` occurs in at most
`|C| - 2` selected rows. -/
lemma polynomialCircuitSelection
    {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (A : ι → Finset β) (t : ℕ) (hA : ∀ i, (A i).card = t)
    (hι : t + 2 ≤ Fintype.card ι) (hβ : t + 2 ≤ Fintype.card β) :
    ∃ C : Finset ι, ∃ Y : Finset β,
      C.card + Y.card = t + 2 ∧
      2 ≤ C.card ∧
      ∀ z ∉ Y, (C.filter fun i ↦ z ∈ A i).card ≤ C.card - 2 := by
  classical
  let a : β → ℚ := fun z ↦ ((Fintype.equivFin β z).val : ℚ)
  have ha : Function.Injective a := by
    intro x y hxy
    apply (Fintype.equivFin β).injective
    apply Fin.ext
    exact Rat.natCast_injective hxy
  let p : ι → ℚ[X] := fun i ↦ rootPolynomial a (A i)
  have hpdeg : ∀ i, (p i).natDegree ≤ t := by
    intro i
    simp [p, hA i]
  have hpdep : ¬ LinearIndependent ℚ p := by
    intro hpind
    have hcoeff := linearIndependent_coeffVector t p hpdeg hpind
    have hcard := hcoeff.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
    omega
  obtain ⟨C, hCtwo, hCmin⟩ :=
    exists_minimallyDependent_finset p (fun i ↦ rootPolynomial_ne_zero a (A i)) hpdep
  let AC : C → Finset β := fun i ↦ A i
  let P := commonRoots AC
  have hCnonempty : Nonempty C := Fintype.card_pos_iff.mp (by
    simpa using (show 0 < C.card by omega))
  letI : Nonempty C := hCnonempty
  have hCupper : C.card ≤ t + 2 := by
    have := hCmin.card_le_degree_add_two (fun i : C ↦ p i) t (fun i ↦ hpdeg i)
    simpa using this
  have hP : P.card ≤ t + 2 - C.card := by
    simpa [P] using
      (commonRoots_card_le a AC t (fun i ↦ hA i) (by simpa [AC, p] using hCmin))
  have htarget : t + 2 - C.card ≤ Fintype.card β := by omega
  obtain ⟨Y, hPY, hYcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ P) hP htarget
  refine ⟨C, Y, ?_, hCtwo, ?_⟩
  · omega
  · intro z hzY
    have hzP : z ∉ P := fun hz ↦ hzY (hPY hz)
    have hmissing : ¬ ∀ i : C, z ∈ AC i := by
      intro hall
      apply hzP
      simpa [P, commonRoots] using hall
    push Not at hmissing
    obtain ⟨j, hzj⟩ := hmissing
    obtain ⟨i, hij, hzi⟩ := exists_second_not_mem_of_minimallyDependent
      a ha AC (by simpa [AC, p] using hCmin) hzj
    let N := C.filter fun x ↦ z ∉ A x
    have hpair : ({i.val, j.val} : Finset ι) ⊆ N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨i.property, hzi⟩
      · exact Finset.mem_filter.mpr ⟨j.property, hzj⟩
    have hpCard : ({i.val, j.val} : Finset ι).card = 2 := by
      simp [Subtype.coe_injective.ne hij]
    have hNtwo : 2 ≤ N.card := by
      rw [← hpCard]
      exact Finset.card_le_card hpair
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := C) (fun x ↦ z ∈ A x)
    change (C.filter fun x ↦ z ∈ A x).card + N.card = C.card at hpartition
    omega

end

end Graffiti387
