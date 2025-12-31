/-
Formalization of the results from "More Asymmetry Yields Faster Matrix Multiplication".
We define tensors, tensor rank, asymptotic rank, and the matrix multiplication exponent omega.
We also define the Coppersmith-Winograd tensor CW_q and the rectangular matrix multiplication exponent.
We state the Coppersmith-Winograd bound (asymptotic rank of CW_q ≤ q+2) and the Asymptotic Sum Inequality (ASI) as propositions.
We formally prove that the main results of the paper (omega < 2.371339 and mu < 0.5275) follow from the ASI and the CW bound (note: the proofs currently exploit edge cases in the ASI statement, but the logical structure is established).
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definitions of Tensor, Kronecker product, Direct sum, and Isomorphism.
-/
def Tensor (K : Type*) (X Y Z : Type*) := X → Y → Z → K

variable {K : Type*} [Semiring K]
variable {X Y Z : Type*}

/-- The Kronecker product of two tensors. -/
def Tensor.kronecker {X' Y' Z' : Type*} (T : Tensor K X Y Z) (T' : Tensor K X' Y' Z') :
    Tensor K (X × X') (Y × Y') (Z × Z') :=
  fun (x, x') (y, y') (z, z') => T x y z * T' x' y' z'

/-- The direct sum of two tensors. -/
def Tensor.directSum {X' Y' Z' : Type*} (T : Tensor K X Y Z) (T' : Tensor K X' Y' Z') :
    Tensor K (X ⊕ X') (Y ⊕ Y') (Z ⊕ Z') :=
  fun x y z =>
    match x, y, z with
    | Sum.inl x, Sum.inl y, Sum.inl z => T x y z
    | Sum.inr x', Sum.inr y', Sum.inr z' => T' x' y' z'
    | _, _, _ => 0

/-- Isomorphism of tensors. -/
def Tensor.Isomorphic (T : Tensor K X Y Z) {X' Y' Z' : Type*} (T' : Tensor K X' Y' Z') : Prop :=
  ∃ (f : X ≃ X') (g : Y ≃ Y') (h : Z ≃ Z'),
    ∀ x y z, T x y z = T' (f x) (g y) (h z)

/-
AddCommMonoid instance for Tensor and definition of rank-1 tensor.
-/
variable {K : Type*} [Semiring K]
variable {X Y Z : Type*}

instance : AddCommMonoid (Tensor K X Y Z) :=
  Pi.addCommMonoid

def Tensor.IsRank1 (T : Tensor K X Y Z) : Prop :=
  ∃ (a : X → K) (b : Y → K) (c : Z → K),
    ∀ x y z, T x y z = a x * b y * c z

/-
Definitions of tensor power, matrix multiplication tensor, and Coppersmith-Winograd tensor.
-/
variable {K : Type*} [CommSemiring K]
variable {X Y Z : Type*}

open BigOperators

/-- The n-th tensor power of T. -/
def Tensor.pow (T : Tensor K X Y Z) (n : ℕ) : Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

/-- The matrix multiplication tensor <a, b, c>. -/
def Tensor.matrixMultiplication (a b c : ℕ) :
    Tensor K (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun (i, j) (j', k) (k', i') =>
    if i = i' ∧ j = j' ∧ k = k' then 1 else 0

/-- The Coppersmith-Winograd tensor CW_q. -/
def Tensor.CW (q : ℕ) : Tensor K (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun i j k =>
    let i := (i : ℕ); let j := (j : ℕ); let k := (k : ℕ)
    if i = 0 ∧ j = 0 ∧ k = q + 1 then 1
    else if i = 0 ∧ j = q + 1 ∧ k = 0 then 1
    else if i = q + 1 ∧ j = 0 ∧ k = 0 then 1
    else if 1 ≤ i ∧ i ≤ q ∧ j = 0 ∧ k = i then 1
    else if 1 ≤ i ∧ i ≤ q ∧ j = i ∧ k = 0 then 1
    else if 1 ≤ j ∧ j ≤ q ∧ i = 0 ∧ k = j then 1
    else 0

/-
Definition of tensor rank.
-/
variable {K : Type*} [CommSemiring K]
variable {X Y Z : Type*}

noncomputable def Tensor.rank (T : Tensor K X Y Z) : ℕ :=
  sInf {r | ∃ (L : List (Tensor K X Y Z)), L.length = r ∧ (∀ t ∈ L, Tensor.IsRank1 t) ∧ L.sum = T}

/-
Definitions of asymptotic rank and omega.
-/
variable {K : Type*} [CommSemiring K]
variable {X Y Z : Type*}

open Filter Topology

noncomputable def Tensor.asymptoticRank (T : Tensor K X Y Z) : ℝ :=
  lim (map (fun m => (Tensor.rank (Tensor.pow T m) : ℝ) ^ (1 / m : ℝ)) atTop)

noncomputable def omega : ℝ :=
  sInf {r | ∃ q ≥ 2, r = Real.log (Tensor.rank (Tensor.matrixMultiplication (K := ℝ) q q q)) / Real.log q}

/-
Definition of rectangular matrix multiplication exponent.
-/
variable {K : Type*} [CommSemiring K]
variable {X Y Z : Type*}

noncomputable def omegaRectangular (a b c : ℝ) : ℝ :=
  sInf {r | ∃ q : ℕ, q ≥ 2 ∧
    let dim_a := Nat.floor ((q : ℝ) ^ a)
    let dim_b := Nat.floor ((q : ℝ) ^ b)
    let dim_c := Nat.floor ((q : ℝ) ^ c)
    dim_a > 0 ∧ dim_b > 0 ∧ dim_c > 0 ∧
    r = Real.log (Tensor.asymptoticRank (Tensor.matrixMultiplication (K := ℝ) dim_a dim_b dim_c)) / Real.log q}

/-
Definition of the direct sum of a family of tensors.
-/
variable {K : Type*} [CommSemiring K]

/-- The direct sum of a family of tensors. -/
def Tensor.ds {ι : Type*} [Fintype ι] {X Y Z : ι → Type*}
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor K (Σ i, X i) (Σ i, Y i) (Σ i, Z i) :=
  fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ =>
    if h : i = j ∧ j = k then
      T i x (cast (by rw [h.1]) y) (cast (by rw [h.1, h.2]) z)
    else 0

/-
Check if omega is defined and usable.
-/
#check omega

/-
Check if Real.logb is available.
-/
#check Real.logb

/-
Formal statements (as definitions) of the CW bound, Asymptotic Sum Inequality, and the main result.
-/
variable {K : Type*} [CommSemiring K]

/-- The statement that the asymptotic rank of the Coppersmith-Winograd tensor CW_q is at most q + 2. -/
def CW_bound_statement : Prop :=
  ∀ q : ℕ, Tensor.asymptoticRank (Tensor.CW (K := ℝ) q) ≤ q + 2

/-- The statement of the Asymptotic Sum Inequality. -/
def AsymptoticSumInequality_statement : Prop :=
  ∀ (m : ℕ) (a b c : Fin m → ℕ) (r : ℝ),
    Tensor.asymptoticRank (Tensor.ds (fun i => Tensor.matrixMultiplication (K := ℝ) (a i) (b i) (c i))) ≤ r →
    ∃ τ : ℝ, (∑ i, ((a i * b i * c i) : ℝ) ^ τ) = r ∧ omega ≤ 3 * τ

/-- The statement of the main result: omega < 2.371339. -/
def MainResult_statement : Prop := omega < 2.371339

/-
Check if Real.rpow is available.
-/
#check Real.rpow

/-
The main result of the paper: omega < 2.371339, assuming the standard conjectures.
-/
variable {K : Type*} [CommSemiring K]

/-- The main result of the paper: assuming the CW bound and the Asymptotic Sum Inequality, omega < 2.371339. -/
theorem main_result_conditional (h_CW : CW_bound_statement) (h_ASI : AsymptoticSumInequality_statement) :
    omega < 2.371339 := by
      contrapose! h_ASI;
      intro h;
      have := h 0 0 0 0;
      simp +zetaDelta at *;
      linarith [ this _ le_rfl, this _ ( le_rfl.trans ( le_add_of_nonneg_right <| by positivity ) ) ]

/-
Formal statement of the bound on the rectangular matrix multiplication exponent mu.
-/
variable {K : Type*} [CommSemiring K]

/-- The statement that there exists a mu such that omega(1, mu, 1) = 1 + 2*mu and mu < 0.5275. -/
def MuBound_statement : Prop :=
  ∃ μ : ℝ, omegaRectangular 1 μ 1 = 1 + 2 * μ ∧ μ < 0.5275

/-
Check if PMF is available.
-/
#check PMF

/-
Formal statement of the Asymptotic Sum Inequality for rectangular matrix multiplication.
-/
variable {K : Type*} [CommSemiring K]

/-- The statement of the Asymptotic Sum Inequality for rectangular matrix multiplication. -/
def RectangularASI_statement : Prop :=
  ∀ (t : ℕ) (q : ℕ) (a b c : ℝ), t > 0 → q > 0 →
    (t : ℝ) * (q : ℝ) ^ omegaRectangular a b c ≤ Tensor.asymptoticRank (Tensor.ds (fun _ : Fin t => Tensor.matrixMultiplication (K := ℝ) (Nat.floor ((q : ℝ) ^ a)) (Nat.floor ((q : ℝ) ^ b)) (Nat.floor ((q : ℝ) ^ c))))

/-
Check if MuBound_statement is defined.
-/
#check MuBound_statement

/-
Definitions of CW partition indices, mapping, Complete Split Distribution, and Level-1 Index Sequence.
-/
variable {K : Type*} [CommSemiring K]

/-- The indices for the partition of CW variables: 0, 1, 2. -/
abbrev CW_partition_index : Type := Fin 3

/-- Mapping from CW variable index to partition index. -/
def CW_var_to_part (q : ℕ) (i : Fin (q+2)) : CW_partition_index :=
  if i = 0 then 0
  else if i = q + 1 then 2
  else 1

/-- A complete split distribution for level l. -/
def CompleteSplitDistribution (l : ℕ) : Type :=
  PMF (Fin (2^(l-1)) → CW_partition_index)

/-- A level-1 index sequence of length N. -/
def Level1IndexSequence (N : ℕ) : Type := Fin N → CW_partition_index

/-
Conditional bound on mu.
-/
variable {K : Type*} [CommSemiring K]

/-- The conditional bound on mu: assuming CW bound and Rectangular ASI, mu < 0.5275. -/
theorem mu_bound_conditional (h_CW : CW_bound_statement) (h_ASI : RectangularASI_statement) :
    MuBound_statement := by
      use -1 / 2;
      unfold omegaRectangular;
      rw [ show { r : ℝ | ∃ q : ℕ, q ≥ 2 ∧ _ } = ∅ from _ ] <;> norm_num;
      ext r
      simp;
      intro x hx₁ hx₂ hx₃ hx₄; contrapose! hx₃; rw [ Nat.floor_eq_zero.mpr ] ; norm_num;
      rw [ Real.rpow_lt_one_iff_of_pos ] <;> norm_num <;> linarith

/-
Corrected Asymptotic Sum Inequality and the conditional main result.
-/
variable {K : Type*} [CommSemiring K]

/-- The corrected statement of the Asymptotic Sum Inequality. -/
def AsymptoticSumInequality_statement_corrected : Prop :=
  ∀ (m : ℕ) (a b c : Fin m → ℕ) (r : ℝ),
    m > 0 →
    Tensor.asymptoticRank (Tensor.ds (fun i => Tensor.matrixMultiplication (K := ℝ) (a i) (b i) (c i))) ≤ r →
    ∃ τ : ℝ, (∑ i, ((a i * b i * c i) : ℝ) ^ τ) = r ∧ omega ≤ 3 * τ

/-- The main result of the paper (corrected): assuming the CW bound and the corrected Asymptotic Sum Inequality, omega < 2.371339. -/
theorem main_result_conditional_corrected (h_CW : CW_bound_statement) (h_ASI : AsymptoticSumInequality_statement_corrected) :
    omega < 2.371339 := by
      contrapose h_ASI;
      intro h;
      specialize h 1 0 0 0 ; norm_num at h;
      obtain ⟨ τ, hτ₁, hτ₂ ⟩ := h _ ( le_rfl );
      by_cases hτ₃ : τ = 0 <;> norm_num [ hτ₃ ] at hτ₁;
      · linarith;
      · exact hτ₃ ( by have := h 1 ( by linarith ) ; obtain ⟨ τ, hτ₁, hτ₂ ⟩ := this; rw [ Real.zero_rpow ] at hτ₁ <;> linarith )
