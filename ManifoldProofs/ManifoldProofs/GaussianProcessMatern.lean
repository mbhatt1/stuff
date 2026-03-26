/-
  GaussianProcessMatern.lean

  Lean 4 / Mathlib-compatible formalization of Gaussian Processes with the
  Matern 5/2 kernel, as used in the paper "Manifold of Failure."

  The paper fits a GP with Matern kernel (nu = 5/2) to observed data and
  uses the posterior mean and variance to model unvisited cells.

  The Matern 5/2 kernel is:
    k(r) = sigma^2 * (1 + sqrt(5)*r/l + 5*r^2/(3*l^2)) * exp(-sqrt(5)*r/l)
  where r = ||x - x'||.

  We formalize:
    1. Positive-definite kernels via the Gram matrix condition
    2. The Matern 5/2 kernel formula
    3. Positive-definiteness of the Matern 5/2 kernel (stated as axiom)
    4. Gaussian Processes as consistent finite-dimensional Gaussian families
    5. GP posterior mean:  mu*(x) = k(x, X) K^{-1} y
    6. GP posterior variance: sigma^2*(x) = k(x,x) - k(x,X) K^{-1} k(X,x)
    7. Non-negativity of the posterior variance

  Proofs requiring heavy linear algebra machinery use `sorry`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Basic

open Matrix Real BigOperators

noncomputable section

-- ============================================================================
-- Section 1: Positive-Definite Kernels
-- ============================================================================

/-- A kernel on a type `X` is a symmetric function `X x X -> R`. -/
structure Kernel (X : Type*) where
  /-- The kernel function mapping pairs of points to real values. -/
  toFun : X -> X -> Real
  /-- Kernels are symmetric: k(x, y) = k(y, x). -/
  symmetric' : forall (x y : X), toFun x y = toFun y x

instance {X : Type*} : CoeFun (Kernel X) (fun _ => X -> X -> Real) :=
  ⟨Kernel.toFun⟩

/-- The Gram matrix of a kernel `k` evaluated at a finite list of points.
    G_{i,j} = k(x_i, x_j) for points x_0, ..., x_{n-1}. -/
def gramMatrix {X : Type*} (k : Kernel X) {n : Nat} (points : Fin n -> X) :
    Matrix (Fin n) (Fin n) Real :=
  Matrix.of (fun i j => k points[i] points[j])

/-- A kernel is positive semidefinite if for every finite collection of points,
    the Gram matrix is positive semidefinite: for all vectors v,
    v^T G v >= 0. -/
def Kernel.IsPositiveSemidefinite {X : Type*} (k : Kernel X) : Prop :=
  forall (n : Nat) (points : Fin n -> X),
    (gramMatrix k points).PosSemidef

/-- A kernel is (strictly) positive definite if for every finite collection of
    *distinct* points, the Gram matrix is positive definite: for all nonzero
    vectors v, v^T G v > 0. -/
def Kernel.IsPositiveDefinite {X : Type*} [DecidableEq X] (k : Kernel X) : Prop :=
  forall (n : Nat) (points : Fin n -> X),
    Function.Injective points ->
    (gramMatrix k points).PosDef

/-- Positive definiteness implies positive semidefiniteness. -/
theorem Kernel.IsPositiveDefinite.toPosSemidef {X : Type*} [DecidableEq X]
    (k : Kernel X) (hk : k.IsPositiveDefinite) : k.IsPositiveSemidefinite :=
  sorry

-- ============================================================================
-- Section 2: The Matern 5/2 Kernel
-- ============================================================================

/-- Parameters for the Matern 5/2 kernel. -/
structure MaternParams where
  /-- Signal variance (sigma^2 > 0). -/
  signalVariance : Real
  /-- Length scale (l > 0). -/
  lengthScale : Real
  /-- Signal variance is positive. -/
  signalVariance_pos : 0 < signalVariance
  /-- Length scale is positive. -/
  lengthScale_pos : 0 < lengthScale

/-- The Matern 5/2 kernel function. Given distance r >= 0, parameters sigma^2
    and l, the kernel value is:
      k(r) = sigma^2 * (1 + sqrt(5)*r/l + 5*r^2/(3*l^2)) * exp(-sqrt(5)*r/l)
    This is the radial part; the full kernel is k(x, x') = k(||x - x'||). -/
def matern52_radial (p : MaternParams) (r : Real) : Real :=
  let sqrt5 := Real.sqrt 5
  let scaled := sqrt5 * r / p.lengthScale
  p.signalVariance * (1 + scaled + 5 * r ^ 2 / (3 * p.lengthScale ^ 2)) *
    Real.exp (-scaled)

/-- The Matern 5/2 kernel on a metric space X.
    k(x, x') = matern52_radial(||x - x'||). -/
def matern52Kernel {X : Type*} [PseudoMetricSpace X] (p : MaternParams) :
    Kernel X where
  toFun := fun x y => matern52_radial p (dist x y)
  symmetric' := fun x y => by simp [matern52_radial, dist_comm]

/-- The Matern 5/2 kernel evaluated at zero distance returns the signal
    variance: k(x, x) = sigma^2. -/
theorem matern52_at_zero {X : Type*} [PseudoMetricSpace X]
    (p : MaternParams) (x : X) :
    (matern52Kernel p) x x = p.signalVariance := by
  simp [matern52Kernel, matern52_radial, dist_self]
  ring_nf
  simp [Real.exp_zero]
  ring

/-- The Matern 5/2 kernel is non-negative for non-negative distances. -/
theorem matern52_radial_nonneg (p : MaternParams) {r : Real} (hr : 0 <= r) :
    0 <= matern52_radial p r :=
  sorry

-- ============================================================================
-- Section 3: Positive-Definiteness of the Matern 5/2 Kernel (Axiom)
-- ============================================================================

/-- **Theorem (Positive-definiteness of the Matern 5/2 kernel).**
    The Matern 5/2 kernel is a positive-definite kernel on any Euclidean space.

    This is a classical result following from Bochner's theorem: the Matern
    kernel is the Fourier transform of a positive spectral density
    (a Student-t density), and Bochner's theorem guarantees that any
    continuous stationary kernel whose spectral measure is a positive finite
    measure is positive definite.

    A full formal proof would require:
    - Bochner's theorem (characterization of positive-definite functions
      via their Fourier transform)
    - The spectral density of the Matern kernel
    - Integration theory connecting the spectral density to the kernel

    We state this as an axiom. -/
axiom matern52_isPositiveDefinite
    {d : Nat} (p : MaternParams) :
    (matern52Kernel (X := EuclideanSpace Real (Fin d)) p).IsPositiveDefinite

/-- Corollary: the Matern 5/2 kernel is positive semidefinite. -/
theorem matern52_isPosSemidef
    {d : Nat} (p : MaternParams) :
    (matern52Kernel (X := EuclideanSpace Real (Fin d)) p).IsPositiveSemidefinite :=
  Kernel.IsPositiveDefinite.toPosSemidef _ (matern52_isPositiveDefinite p)

-- ============================================================================
-- Section 4: Gaussian Processes
-- ============================================================================

/-- A Gaussian Process specification over an index set `X`. A GP is
    determined by its mean function and covariance kernel. Any finite
    marginal (f(x_1), ..., f(x_n)) is multivariate Gaussian with
    mean vector mu and covariance matrix K.

    We define the GP by its defining data (mean function + kernel) and
    axiomatize the existence of a consistent probability measure. -/
structure GaussianProcess (X : Type*) where
  /-- The mean function mu: X -> R. -/
  meanFun : X -> Real
  /-- The covariance kernel. -/
  covKernel : Kernel X
  /-- The covariance kernel must be positive semidefinite (necessary and
      sufficient for the existence of a consistent GP measure, by
      Kolmogorov's extension theorem). -/
  kernel_posSemidef : covKernel.IsPositiveSemidefinite

/-- A zero-mean GP, the most common prior in practice. -/
def zeroMeanGP {X : Type*} (k : Kernel X) (hk : k.IsPositiveSemidefinite) :
    GaussianProcess X where
  meanFun := fun _ => 0
  covKernel := k
  kernel_posSemidef := hk

/-- A zero-mean GP with the Matern 5/2 kernel on Euclidean space. -/
def maternGP {d : Nat} (p : MaternParams) :
    GaussianProcess (EuclideanSpace Real (Fin d)) :=
  zeroMeanGP (matern52Kernel p) (matern52_isPosSemidef p)

-- ============================================================================
-- Section 5: GP Posterior (Conditioning on Observations)
-- ============================================================================

/-- Given a GP, `n` training points, and observed values, the GP posterior
    is characterized by closed-form mean and variance formulas.

    Training data: points x_1, ..., x_n with observations y_1, ..., y_n.
    The posterior at a new point x* is:

      mu*(x*) = k(x*, X) @ K^{-1} @ y
      sigma^2*(x*) = k(x*, x*) - k(x*, X) @ K^{-1} @ k(X, x*)

    where:
      K = Gram matrix [k(x_i, x_j)]_{i,j}
      k(x*, X) = row vector [k(x*, x_1), ..., k(x*, x_n)]
      k(X, x*) = column vector [k(x_1, x*), ..., k(x_n, x*)]^T
      y = observation vector [y_1, ..., y_n]^T
-/

/-- The cross-covariance vector k(x*, X): the vector of kernel evaluations
    between a query point and each training point. -/
def crossCovVector {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (queryx : X) : Fin n -> Real :=
  fun i => k queryx (trainPoints i)

/-- Convert a function `Fin n -> R` to a column vector (n x 1 matrix). -/
def toColVec {n : Nat} (v : Fin n -> Real) : Matrix (Fin n) (Fin 1) Real :=
  Matrix.of (fun i _ => v i)

/-- Convert a function `Fin n -> R` to a row vector (1 x n matrix). -/
def toRowVec {n : Nat} (v : Fin n -> Real) : Matrix (Fin 1) (Fin n) Real :=
  Matrix.of (fun _ j => v j)

/-- The GP posterior mean at a query point x*, given training data.
    mu*(x*) = k(x*, X) @ K^{-1} @ y

    Here K is the Gram matrix of the kernel at the training points,
    and y is the vector of observations. -/
def gpPosteriorMean {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (observations : Fin n -> Real)
    (queryx : X) : Real :=
  let K := gramMatrix k trainPoints
  let kstar := crossCovVector k trainPoints queryx
  let Kinv := K⁻¹
  -- mu*(x*) = sum_i sum_j kstar_i * Kinv_{i,j} * y_j
  -- Equivalently: kstar^T @ Kinv @ y, which is a scalar.
  let weights := Kinv.mulVec (fun i => observations i)
  Finset.sum Finset.univ (fun i => kstar i * weights i)

/-- The GP posterior variance at a query point x*, given training data.
    sigma^2*(x*) = k(x*, x*) - k(x*, X) @ K^{-1} @ k(X, x*)

    This represents the remaining uncertainty after conditioning on
    the observations. -/
def gpPosteriorVariance {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X)
    (queryx : X) : Real :=
  let K := gramMatrix k trainPoints
  let kstar := crossCovVector k trainPoints queryx
  let Kinv := K⁻¹
  -- k(x*, x*) - k(x*, X) @ K^{-1} @ k(X, x*)
  let KinvKstar := Kinv.mulVec kstar
  let quadForm := Finset.sum Finset.univ (fun i => kstar i * KinvKstar i)
  k queryx queryx - quadForm

/-- Bundle of GP posterior predictions at a query point. -/
structure GPPrediction where
  /-- Posterior mean. -/
  mean : Real
  /-- Posterior variance. -/
  variance : Real

/-- Compute the full GP posterior prediction at a query point. -/
def gpPredict {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (observations : Fin n -> Real)
    (queryx : X) : GPPrediction where
  mean := gpPosteriorMean k trainPoints observations queryx
  variance := gpPosteriorVariance k trainPoints queryx

-- ============================================================================
-- Section 6: Properties of the GP Posterior
-- ============================================================================

/-- **Theorem: The GP posterior variance is non-negative.**

    This follows from the Schur complement characterization of positive
    semidefiniteness. The augmented Gram matrix (including the query point)
    is positive semidefinite. The Schur complement of the training block K
    in this augmented matrix is exactly:
      k(x*, x*) - k(x*, X) K^{-1} k(X, x*)
    and Schur complements of PSD matrices are PSD (i.e., non-negative for
    the 1x1 case).

    A full proof would require:
    - The Gram matrix of a PSD kernel at any finite set is PSD
    - The Schur complement lemma for positive semidefinite matrices
    - Invertibility of the training Gram matrix (or use of pseudoinverse)
-/
theorem gpPosteriorVariance_nonneg {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (hInj : Function.Injective trainPoints)
    (queryx : EuclideanSpace Real (Fin d)) :
    0 <= gpPosteriorVariance (matern52Kernel p) trainPoints queryx :=
  sorry

/-- The posterior variance at a training point is zero (assuming no noise
    and the Gram matrix is invertible). That is, the GP interpolates exactly
    through the training data. -/
theorem gpPosteriorVariance_at_training_point {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (hInj : Function.Injective trainPoints)
    (i : Fin n) :
    gpPosteriorVariance (matern52Kernel p) trainPoints (trainPoints i) = 0 :=
  sorry

/-- The posterior variance is bounded above by the prior variance k(x*, x*).
    Observing data can only reduce uncertainty. -/
theorem gpPosteriorVariance_le_prior {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (hInj : Function.Injective trainPoints)
    (queryx : EuclideanSpace Real (Fin d)) :
    gpPosteriorVariance (matern52Kernel p) trainPoints queryx <=
      (matern52Kernel p) queryx queryx :=
  sorry

/-- The prior variance equals the signal variance parameter. -/
theorem gpPosteriorVariance_prior_eq_signalVariance {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (hInj : Function.Injective trainPoints)
    (queryx : EuclideanSpace Real (Fin d)) :
    (matern52Kernel p) queryx queryx = p.signalVariance :=
  matern52_at_zero p queryx

/-- Combining the above: the posterior variance is bounded in [0, sigma^2]. -/
theorem gpPosteriorVariance_bounded {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (hInj : Function.Injective trainPoints)
    (queryx : EuclideanSpace Real (Fin d)) :
    0 <= gpPosteriorVariance (matern52Kernel p) trainPoints queryx /\
    gpPosteriorVariance (matern52Kernel p) trainPoints queryx <=
      p.signalVariance := by
  constructor
  · exact gpPosteriorVariance_nonneg p trainPoints hInj queryx
  · calc gpPosteriorVariance (matern52Kernel p) trainPoints queryx
        <= (matern52Kernel p) queryx queryx :=
          gpPosteriorVariance_le_prior p trainPoints hInj queryx
      _ = p.signalVariance :=
          gpPosteriorVariance_prior_eq_signalVariance p trainPoints hInj queryx

-- ============================================================================
-- Section 7: Noisy Observations (Gaussian Likelihood)
-- ============================================================================

/-- In practice, observations include noise: y_i = f(x_i) + epsilon_i
    where epsilon_i ~ N(0, sigma_n^2). The noisy Gram matrix is K + sigma_n^2 I.

    This modifies the posterior formulas:
      mu*(x*) = k(x*, X) (K + sigma_n^2 I)^{-1} y
      sigma^2*(x*) = k(x*, x*) - k(x*, X) (K + sigma_n^2 I)^{-1} k(X, x*)
-/

/-- The noisy Gram matrix: K + sigma_n^2 * I. -/
def noisyGramMatrix {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (noiseVariance : Real) :
    Matrix (Fin n) (Fin n) Real :=
  gramMatrix k trainPoints + noiseVariance • (1 : Matrix (Fin n) (Fin n) Real)

/-- GP posterior mean with noisy observations. -/
def gpPosteriorMeanNoisy {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (observations : Fin n -> Real)
    (noiseVariance : Real) (queryx : X) : Real :=
  let Knoisy := noisyGramMatrix k trainPoints noiseVariance
  let kstar := crossCovVector k trainPoints queryx
  let Kinv := Knoisy⁻¹
  let weights := Kinv.mulVec (fun i => observations i)
  Finset.sum Finset.univ (fun i => kstar i * weights i)

/-- GP posterior variance with noisy observations. -/
def gpPosteriorVarianceNoisy {X : Type*} (k : Kernel X) {n : Nat}
    (trainPoints : Fin n -> X) (noiseVariance : Real)
    (queryx : X) : Real :=
  let Knoisy := noisyGramMatrix k trainPoints noiseVariance
  let kstar := crossCovVector k trainPoints queryx
  let Kinv := Knoisy⁻¹
  let KinvKstar := Kinv.mulVec kstar
  let quadForm := Finset.sum Finset.univ (fun i => kstar i * KinvKstar i)
  k queryx queryx - quadForm

/-- The noisy posterior variance is also non-negative. Adding noise to the
    diagonal makes K + sigma_n^2 I "more invertible" and the Schur complement
    argument still applies. -/
theorem gpPosteriorVarianceNoisy_nonneg {d : Nat}
    (p : MaternParams) {n : Nat}
    (trainPoints : Fin n -> EuclideanSpace Real (Fin d))
    (noiseVariance : Real) (hNoise : 0 < noiseVariance)
    (queryx : EuclideanSpace Real (Fin d)) :
    0 <= gpPosteriorVarianceNoisy (matern52Kernel p) trainPoints
      noiseVariance queryx :=
  sorry

-- ============================================================================
-- Section 8: The Gram Matrix is Symmetric
-- ============================================================================

/-- The Gram matrix of any kernel is symmetric. -/
theorem gramMatrix_symmetric {X : Type*} (k : Kernel X) {n : Nat}
    (points : Fin n -> X) :
    (gramMatrix k points).IsSymm := by
  intro i j
  simp [gramMatrix, Matrix.of_apply]
  exact k.symmetric' (points i) (points j)

end
