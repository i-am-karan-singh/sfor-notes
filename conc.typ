#import "47834.typ": lecture
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *
#set-inherited-levels(0)
  
#show: lecture.with([Basic Concentration Inequalities], 1)
#show: show-theorion
#show link: underline

This course is about both negotiating uncertainty and using randomness in decision making. Most modern-day decision making systems (think, for example, ride-share) operate while dealing with multiple sources of randomness: Can we describe them well using deterministic systems? Do the particulars of uncertainties they are subject to actually matter? What are the aggregate statistical properties of such algorithms? The goal here is to provide just enough foundational knowledge so that the students can dive deeply into these data-driven optimization and algorithm design.

In general, we will weave through a potpourri of topics. We will start with _basic concentration inequalities_ in the first week and discuss _Bayesian statistics and causal inference_ the week after. After switching to a couple of weeks on _statistical learning_ and _sequential prediction_, we will survey _statistical fairness_ in the decision-making context. The final topic will be the _information-theoretic limits_ of performance for data-driven algorithms.

#outline()

= Convexity
#definition[
    A set $S subset.eq$ vector space $V$ is *convex* if for all $x, y in S$ and $lambda in [0,1]$, $lambda x + (1-lambda) y in S$.
]

Note that $S_(x,y) = {lambda x + (1-lambda) y : lambda in [0,1]}$ is a line segment that connects $x$ and $y$. In other words, a convex set contains all line segments whose endpoints lie inside the set.

#definition[
    A function $f: cal(X) arrow RR$, where $cal(X)$ is a convex set, is said to be *convex* if $forall x, y in cal(X)$, $forall lambda in [0,1]$, $f(lambda x + (1-lambda)y) <= lambda f(x) + (1-lambda) f(y)$.
]

In other words, for a convex function, the function value at any interpolation is (weakly) less than the interpolated function values.

#definition[
    The convex hull of a set $X subset.eq $ some vector space $V$ is the smallest convex set that contains X.
]

Here, the notion of smallness is with respect to inclusion, that is, $A$ is smaller than $B$ if $A subset B$. Therefore, incomparable sets exist; nevertheless, the smallest is well defined. If $X={x_1,x_2,dots x_m}$ is finite, the convex hull becomes ${sum_(i=1)^m alpha_i x_i: sum_(i=1)^m alpha_i = 1, alpha_i >= 0, forall i in [m]}$.

= Probability
A probability measure is described by $(Omega,cal(F),Pr)$, where $Omega$ is the outcome space, $cal(F) subset.eq 2^Omega$ is the set of measurable subsets of $Omega$, and $P:cal(F) arrow [0,1]$ assigns probability to the sets in $cal(F)$. The three rules for $P$ are: it must be non-negative, it must assign measure one to $Omega$, and it must be additive on any collection of countably many disjoint sets  in $cal(F)$. In this course, it is okay to think of $cal(F)=2^Omega$; this is true, for example, for discrete outcomes. We will avoid measurability issues by assuming that you know what expectation is.

#lemma[
  For any two real-valued random variables $X, Y,$ $EE[X+Y] = EE[X]+EE[Y]$.
]

Recall that a collection of random variables ${X_i}_(i in cal(I))$ is independent if $Pr(X_i in S_i)_(i in cal(I)) = Pi_(i in cal(I)) Pr(X_i in S_i)$. A weaker condition is pairwise independence, which only requires that for all pairs $X_1, X_2 in {X_i}_(i in cal(I))$, we have $Pr(X_1 in S_1, X_2 in S_2) = Pr(X_2 in S_1)Pr(X_2 in S_2)$. 

Recall that the variance of $X$ is defined as $VV[X] = EE [(X-EE[X])^2]$. Using this, we observe that for independent random variables $X,Y$, we have $
VV[X+Y] = EE[(X-EE X+Y-EE Y)^2] = VV[X] + VV[Y] + 2 underbrace(EE[X-EE X],=0) EE[Y-EE Y] = VV[X] + VV[Y].
$ In fact, the additivity of variance, over any number of random variables, only requires pairwise independence.

#exercise[
  Prove that $VV[X] = EE[X^2] - (EE[X])^2 = min_(a in RR)EE[(X-a)^2] = 1/2 EE[(X-X')^2]$, where $X'$ is an independent copy of $X$.
]

= Approximate Caratheodory's Theorem
In convex geometry, Caratheodory's theorem states that, given a set of any size in $RR^d$, any point in its convex hull can be written as a convex combination of $d+1$ points. Notice that there is no dependence on the number of points in the original set. In two dimensions, you can convince yourself that this is true by noting that any convex polygon can be perfectly decomposed into non-overlapping triangles by connecting the vertices in the correct way; thus, any point in a convex polygon lies in a triangle supported on the vertices of the polygon.

Such theorems are results about minimal representations: how many elements are needed to represent any point from a rich set? We will prove another such result that uses far fewer points, in fact, independent of the dimension, given a small slack.

#theorem(title: "Approximate Caratheodory's")[
    Let $X$ be a set in $RR^d$ contained in the unit ball $BB_2={x:norm(x)_2<= 1}$. For any $k>= 0$ and $y$ in the convex hull of $X$, there exist $k$ points $z_1, dots z_k in X$ such that $
    norm(y - 1/k sum_(i=1)^k z_k)_2 <= 1/sqrt(k).
    $
]

Thus, if we are willing to tolerate $epsilon$ slack in how well $x$ is approximated, $1/epsilon^2$ points suffice. In fact, note that our convex combination is also _special_, being a simple average. 

#proof[
    Since $y$ is the convex hull, we know that $y=sum_(i=1)^m alpha_i x_i$ for some $x_1, x_2,dots x_m in X$, where $alpha_i>=0$ sum to one. Consider a random variable $Z_1$ that picks $x_i$ with probability $alpha_i$ for all $i in [m]$. Notice that by definition $EE[Z_1]=y$. Consider $Z_2, dots Z_k$ additional independent copies of $Z_1$. Now $
    EE norm(1/k sum_(i=1)^k Z_i - y)^2_2 = 1/k^2 sum_(i=1)^k EE norm(Z_i-y)^2_2 = 1/k (EE norm(Z_1)_2^2 - norm(y)_2^2) <= 1/k.
    $ Thus, there must exist some realization of $Z_1,dots Z_k$ such that $norm(1/k sum_(i=1)^k Z_i - y)_2^2<= 1/k$.
]

== Application: Choice Models
Human behavior is tricky and often inconsistent. Choice models study statistical models of the same. For example, in the Plackett-Luce model, with a universe of $n$ products, it is assumed that a tester given items $i$ and $j$ will prefer $i$ over $j$ with probability $w_i slash (w_i+w_j)$. Given a lot of such empirical observations, the task is to recover the underlying quality $w_i$ of the items. 

Here, we consider a (nonparametric) model for ranking. Imagine a universe of $n$ products, where it is assumed that the testers are identical and randomly pick a ranking of all products, i.e., $Pr(pi) = sum_(i=1)^(n!) alpha_i bold(1)_(pi=pi_i)$, where we $pi_i$'s are all $n!$ permutations. But instead of receiving direct observations of many such stochastic rankings, we receive a summary statistic: a matrix $Z in [0,1]^(n times n)$ where $Z_(i j)$ represents the fraction of times the product $i$ earned the rank $j$. Farias, Jagathabula and Shah considered the following question: can we produce a choice model that explains the observed matrix? Their main result is that a linearly sparse model is sufficient for this purpose. We will recover this as an implication.

We begin with an application of Caratheodory's theorem. A nonnegative matrix is said to be _doubly stochastic_ if row and column sums are one. $Z$ is such a matrix. Each permutation $pi$ can be written as a permutation matrix $Pi in {0,1}^(n times n)$ where $Pi_(i j)$ if and only if the element $i$ occurs in position $j$ in $pi$. For example $(2, 4, 3, 1)$ can be encoded as $
mat(
  0, 0, 0, 1;
  1, 0, 0, 0;
  0, 0, 1, 0;
  0, 1, 0, 0
)
$ Notice that such matrices are also doubly stochastic, since there is exactly one $1$ in each row and column. A very fundamental result is as follows:

#theorem(title: "Birkhoff-von-Neumann")[
  The convex hull of all permutation matrices is precisely the set of doubly stochastic matrices.
]

By Caratheodory's, any such $Z$ can be written as the convex combination of $(n-1)^2 + 1$ permutation matrices. Thus, any $Z$ can be explained away with a distribution supported on just $(n-1)^2+1$ matrices, an exponentially small fraction of the original $n!$ parameters. Perhaps a bound of $n^2 + 1$ is easier. The precise number comes about by noting that the set of doubly stochastic matrices is $(n-1)^2$-dimensional, given the $(n-1) times (n-1)$ principal sub-matrix, one can always reconstruct the last row and column due to the row and column sum constraints.

Using Approximate Caratheodory's, we can guarantee that there exists a convex combination $Z'$ of $n slash epsilon^2$ permutation matrices such that $norm(Z-Z')_F = sqrt(sum_(i,j in [n]^2) (Z_(i j)-Z'_(i j))^2) <= epsilon$. The additional $n$ factor arises because a permutation matrix has Frobenius norm $sqrt(n)$, and both sides of the inequality in Approximate Caratheodory's grow linearly with the scale.

= Moment Generation Function
Given a random variable $X$, $Psi_X(t) = EE[e^(t X)]$ is defined to be its moment generating function. The MGFs, upon their existence, encode all the moments and vise versa.

#proposition[
    $(d^k)/(d t^k) Psi_X(t)|_(t=0) = EE[X^k e^(t X)]|_(t=0) = EE[X^k]$.
]
*Bernoulli Distribution.* $X tilde "Be"(p)$ is ${0,1}$-valued with $Pr(X=1)=p$. $
Psi_("Be"(p))(t) = (1-p) + p e^t.
$

*Rademacher Distribution.* $X tilde {plus.minus 1}$ is ${plus.minus 1}$-valued with $Pr(X=1)=1/2$. $
Psi_({plus.minus 1})(t) = 1/2 (e^t + e^(-t)) = 1 + (t^2)/2! + t^4/4! + dots <= 1 + sum_(k>= 1) t^(2k)/(2^k k!)= e^(t^2 slash 2).
$

*Gaussian Distribution.* $Z\sim cal(N)(mu,sigma^2)$ if $Z= sigma X + mu$ and $X tilde cal(N)(0,1)$ where $f_(cal(N)(0,1))(x) = 1/(sqrt(2 pi))e^(-x^2 slash 2)$. Recall that $Gamma(k) = integral_0^infinity  t^(k-1)e^(-t) d t$ and $Gamma(k+1) <= k^k$. Now, a few basic facts, where we assume $t,k >= 1$.
$
Psi_(X)(t) = 1/(sqrt(2 pi)) integral e^(t x-x^2 slash 2) d x = (e^(sigma^2 t^2 slash 2))/(sqrt(2 pi)) integral e^(-(x-t)^2 slash 2) d x = e^(t^2 slash 2) \
Psi_((3X^2)/8)(1) = 1/(sqrt(2 pi)) integral e^(3x^2 slash 8 - x^2 slash 2) d x = 1/(sqrt(2 pi)) integral e^(-x^2 slash 8) d x = 2 \
Pr(X>= t) = 1/(sqrt(2 pi)) integral_t^infinity e^(-x^2 slash 2) d x <= 1/(sqrt(2 pi)) integral_t^infinity x/t e^(-x^2 slash 2) d x = 1/(sqrt(2 pi)t) e^(-t^2 slash 2) quad quad  "(Mill's inequality)" \
EE[abs(X)^k] = 1/(sqrt(2 pi)) integral x^k e^(-x^2 slash 2) d x underbrace(=)_(z=x^2 slash 2) (2^(k/2))/(2 sqrt(k pi)) integral z^(k slash 2) e^(-z) d z = (2^(k slash 2))/(2 sqrt(k pi)) Gamma(k slash 2+1) <= C p^(p slash 2)
$

= Why high probability bounds? Why not CLT?
In the future, we will be interested in high-probability tail bounds, where the magnitude of the random deviation scales as $log 1 slash delta$, instead of inverse polynomially in $1 slash delta$. This might be hard to appreciate now, but ultimately, only bounds of the former sort will be useful to control the maximum of a bunch of random variables, which is what we are ultimately building towards.

If $X_1, dots X_n tilde cal(N)(0,1)$, then $1/n sum_(i=1)^n x_i tilde cal(N)(0,1/n)$, and hence $Pr(1/n sum_(i=1)^n x_i>= t) <= e^(-n t^2 slash 2)$.

#theorem(title: "Central Limit Theorem")[
    Consider independent random variables $X_1,X_2 dots$ with mean $mu$ and variance $sigma^2$, then $
    (sum_(i=1)^n (X_i- mu))/(sigma sqrt(n)) arrow cal(N)(0,1)
    $
    that is, their density functions at any level $t$ converge, as $n arrow infinity$.
]
  
CLT says that, in principle, for sufficiently large $n$, appropriately normalized sums behave as if each component is a Gaussian. The tail bound for a Gaussian decay exponentially. What stops us from reducing everything to the Gaussian case? CLT is an asymptotic statement and does not immediately imply anything for a finite number of samples. There is a way to repair this.

#theorem(title: "Berry-Essen")[
    Consider independent random variables $X_1,X_2 dots$ with mean $mu$ and variance $sigma^2$, then for any $t$, $
    abs(Pr((sum_(i=1)^n (X_i-mu))/(sigma sqrt(n)) >= t)- Pr(cal(N)(0,1)>= t)) <= (C EE [abs(X-EE X)^3])/(sigma^3 sqrt(n)).
    $
]

But now, we get $Pr(1/n sum_(i=1)^n x_i- mu >= t) <= e^(-n t^2 slash 2) + (C EE[abs(X-EE X)^3])/(sigma^3 sqrt(n))$, and thus, for the RHS to be at most $delta$, $n>= 1 slash delta^2$, ruling out a dependence of solely $log 1 slash delta$.

= Subgaussian Random Variables
#theorem(title: "Markov's")[
    For a nonnegative RV $X$, for any $t>0$, $
    Pr(X>= t)>= (EE[X])/t.
    $
  ]
#proof[
    Observe $X >= X bold(1)_(X>= t) >= t bold(1)_(X>= t)$. Take expectations on both sides and note $EE[bold(1)_A]=Pr(A)$.
]

#exercise[
  One advantage of using indicator variables and expectations is that your proofs hold as-is for both continuous and discrete random variables, in fact, for mixed ones too. Similarly use indicate variables to prove that $Pr(union_{i in cal(I)) A_i) <= sum_(i in cal(I)) Pr(A_i)$.
]

#exercise[
  Using indicator variables and expectations, prove, for any a nonnegative random variable $X$, that $EE[X] = integral^infinity Pr(X>= t) d t$.
]

#theorem(title: "Chebyshev's")[
    For a RV $X$ with mean $\mu$ and variance $sigma^2$, for any $t>0$, $
    Pr(abs(X-mu)>= t) <= (sigma^2)/(t^2).
    $
]
#proof[
    Apply Markov's starting from $Pr(abs(X- mu) >= t) = Pr((X- mu)^2>= t^2)$.
]

This implies that $Pr(1/n sum_(i=1)^n X_i-mu >= t) <= sigma^2/(n t^2)$, but once again the number of samples is inverse polynomial in $1 slash delta$. To get exponential tail bounds, we define a class of Gaussian-like random variables that have a Gaussian-like tail. Notice that this similarity stops at the tail and does not extend to the body of the distribution unlike CLT. Then, we will prove that this class of RVs is suitably closed under interesting operations, such as averaging.

#definition[
  A random variable X is said to be $sigma^2$-SubGaussian if $EE[e^(t(X-EE X))]<= e^(sigma^2 t^2 slash 2)$.
]

An important note of caution here is that $sigma^2$, being defined in terms of the MGF, in general is not equal to the variance of the SubGaussian distribution. Although this equality does hold for the Gaussian and Rademacher families, in the broadest terms it is merely an upper bound on the variance. 

#lemma(title: "Hoeffding's")[
  Any random variable with support in $[a,b]$ is $((b-a)^2)/4$-SubGaussian.
]
#proof[
  In fact, we will prove a weaker result, but using a technique that we will reuse in the future.$
  EE_X[e^(t(X-EE X))] <= EE_(X,X')[e^(t(X-X'))] = EE_(X,X')EE_(eta tilde {plus.minus 1})[e^(t eta(X-X'))] <= EE_(X,X')e^(t^2(X-X')^2 slash 2) <= e^(t^2(b-a)^2 slash 2)
  $
  Here, the first inequality introduces an independent copy of the random variable $X'$ and follows due to Jensen's, namely that $f(EE X)<= EE f(X)$ for any convex function $f$. The only equality follows by noting that $X-X'$ and $X-X'$ have the same distribution. The second inequality involves the MGF of a Rademacher random variable. Overall, we have only proved the result to be $(b-a)^2$-SubGaussian, but we will use the idea of introducing Rademacher random variables later on, and this is a good first introduction.
]

Using this lemma, any bounded distribution, e.g. Bernoulli, is SubGaussian. Before we move on to concentration inequalities, let us give alternative characterizations of SubGaussian random variables.

#theorem[
  The following four conditions are equivalent, in the sense that all four constants $sigma_1,sigma_2,sigma_3,sigma_4$ are within (universal) constant factors of one another.
  #enum(spacing: 1.5em, indent: 1em)[
    $EE[e^(t(X-EE X))] <= e^(sigma_1^2t^2 slash 2)$
  ][
    $Pr(abs(X - EE X)>= t)<= 2e^(-t^2 slash 2 sigma_2^2)$
  ][
    $(EE[abs(X-EE X)^p])^(1 slash p) <= sigma_3 sqrt(p)$ for all $p>= 1$
  ][
    $EE[e^((X-EE X)^2 slash sigma_4^2)]<= 2$
  ]
]

#proof[
  (1$=>$2) We start with a union bound, and then apply Markov's on the MGF. Because this move is valid for any $t>= 0$, we choose the optimal $t=epsilon slash sigma_1^2$ by minimizing the quadratic. $
  Pr(abs(X-EE X) >= epsilon) &<= 2Pr(X-EE X>= epsilon) = 2 min_(t>= 0) Pr(e^(t(X-EE X)) >= e^(t epsilon)) \
  &<= 2e^(-max_(t>= 0){t epsilon-t^2 sigma_1^2 slash 2}) = 2e^(-epsilon^2 slash 2sigma_1^2)
  $
  (2$=>$3) Recall the $Gamma$ function and that $Gamma(k+1)<= k^k$, and then substitute $t=(2 sigma_2^2 z)^(p slash 2)$.$
  EE abs(X-EE X)^p &= integral_0^infinity Pr(abs(X-EE X)^p>= t) d t = 2integral_0^infinity e^(-t^(2 slash p) slash 2sigma_2^2) d t \
  &= 2^(p slash 2+1) sigma_2^p integral_0^infinity e^(-z) z^(p slash 2-1)d z = 2^(p slash 2+1) sigma_2^p Gamma(p slash 2)
  $
  (3$=>$4) Consider the power series expansion, where we use $k!>= (k slash e)^k$ and substitute $sigma_4 = 2 sqrt(e) sigma_3$. $
  EE[e^((X-EE X)^2 slash sigma_4^2)] = 1+ sum_(k>= 1)(EE[(X-EE X)^(2k)])/(sigma_4^(2k)k!) <= 1+ sum_(k>= 1) (sigma_3^2 2k)^k/(sigma_4^2k/e)^k = 1/(1-2(sigma_3 slash sigma_4)^2e) = 2
  $
  (4$=>$1) This is messy. First, by Taylor's theorem, $e^x <= 1 + x + e^abs(x) x^2/2$. Taking expectation on both sides, we get $
  EE[e^(t(X-EE X))] &<= 1 + t^2/2 EE[(X-EE X)^2e^(t abs(X-EE X))] \
  &<= 1 + t^2/2 EE[(X-EE X)^2e^(sigma_4^2t^2 slash 2)e^((X-EE X)^2 slash 2 sigma_4^2)] & because t x<= (sigma_4^2t^2+x^2 slash sigma_4^2)/2 \
  & <= 1+(sigma_4^2 t^2)/2e^(sigma_4^2 t^2 slash 2) EE[e^((X-EE X)^2 slash sigma_4^2)] <= (1+sigma_4^2 t^2)e^(sigma_4^2 t^2 slash 2) & because x^2 <= e^(x^2 slash 2)\
  &<= e^(3sigma_4^2 t^2 slash 2) & because (1+x) <= e^x.
  
  $
]

Two useful corollaries follow.

#corollary[
  If $X_1 tilde "SubGaussian"(sigma_1^2)$ and $X_2 tilde "SubGaussian"(sigma_2^2)$ are independent random variables, then $X_1+X_2 tilde "SubGaussian"(sigma_1^2+sigma_2^2)$.
]
#proof[
  This follows from noting that for independent RVs $X,Y$, $EE[e^(t(X+Y))]=EE[e^(t X)]EE[e^(t Y)]$ and using the MGF characterization.
]

#corollary[
  If $X_1 tilde "SubGaussian"(sigma_1^2), X_2 tilde "SubGaussian"(sigma_2^2)$, then $X_1+X_2 tilde "SubGaussian"((sigma_1+sigma_2)^2)$.
]
#proof[
  Using the moment characterization, for zero-mean random variables, we get$
  (EE[abs(X_1+X_2)^p])^(1 slash p) <= (EE[abs(X_1)^p])^(1 slash p) + (EE[abs(X_2)^p])^(1 slash p) <= (sigma_1+ sigma_2) sqrt(p),
  $where the first (triangle) inequality follows from the fact that $norm(X)_(L^p) = (EE[abs(X)^p])^(1 slash p)$ is a (semi) norm.
]

= Concentration Inequalities for Linear Forms
#proposition[
  Let ${X_i tilde "SubGaussian"(sigma_i^2)}_(i=1)^n$ be a collection of $n$ independent random variables. Then for any $a in RR^n$, $t>= 0$, we have $
  Pr(abs(sum_(i=1)^n a_i X_i-EE[sum_(i=1)^n a_i X_i])>= t) <= 2e^(-t^2/(2sum_(i=1)^n a_i^2 sigma_i^2)).
  $
]
#proof[
  This follows from $sum_(i=1)^n a_i X_i tilde "SubGaussian"(sum_(i=1)^n a_i^2 sigma_i^2)$, using the penultimate corollary.
]

A common use case is that of averages, that is, when $a_i=1 slash n$.
#corollary[
  Let ${X_i tilde "SubGaussian"(sigma^2)}_(i=1)^n$ be a collection of $n$ identically distributed independent random variables. Then for any $a in RR^n$, $t>= 0$, we have $
  Pr(abs(1/n sum_(i=1)^n X-EE[X])>= t) <= 2e^(-(n t^2)/(2 sigma^2)).
  $ Thus, for any $delta>0$, with probability at least $1-delta$, we have$
  abs(1/n sum_(i=1)^n X_i - EE[X]) <= sqrt((2 sigma^2 log 2/delta)/n).
  $
]
  
The moment generating function was seemingly essential for this bound, but the specific choice $x |-> e^(t X)$ might feel like an accident. Who is to say that we cannot do better? The following result from the theory of large deviations provides some moral support.


#theorem(title: "Cramer")[
  For any sequence of independent and identically sampled random variables $X_1,X_2,dots$ with $Psi(t)=EE[e^(t(X-EE X))]$, we have for any $t>= 0$ that $
  lim_(n-> infinity) 1/n log Pr(1/n sum_(i=1)^n X_i - EE X >= epsilon) >= -max_(t>= 0) {t epsilon- log Psi(t)}.
  $
]

= Maximal Inequalities
#lemma[
    Let ${X_i tilde "SubGaussian"(sigma^2)}_(i=1)^n$ be a collection of $n$ zero-mean random variables. Then, for any $t>= 0$, we have that $
    EE[max_(i<= n) abs(X_i)] <= C sigma sqrt(log n), " and " Pr(max_(i<= n) abs(X_i)>= t) <= 2 n e^(- (t^2)/(2 sigma^2)).
    $
]
#proof[
    The high probability bound follows from a union bound. We will try to prove $
    Pr(max_(i<= n) abs(X_i) >= t) <= 2e^(-t^2/(8 sigma^2 log n)).
    $ If so, then $EE[max_(i<= n) abs(X_i)] <= integral_0^infinity 2e^(-t^2/(8 sigma^2 log n)) d t= C sigma sqrt(log n)$ using the standard Gaussian integral. If $n<= e^(t^2 slash 4 sigma^2)$, substituting this into the union bound suffices. In the other case, the RHS of the needed inequality is at least one, which is a tautology.
] 

= Looking Ahead: Nonlinear Functions
In a few weeks, we will revisit concentration inequalities and arrive at a meta-principle: as long as $X_1, dots X_n$ are independent and $f(X_1, dots X_n)$ is not too sensitive in any of its arguments, we have that $
Pr(|f(X_1, dots X_n) - EE f(X_1,dots X_n)|>t)<= e^(-c n t^2).
$

Formulating this precisely, for different notions of _sensitivities_, will be both easy and difficult. At least one rudimentary form will automatically follow from a Martingale version of the argument we just developed. More sophisticated versions will link to deep mathematical ideas, like isoperimetric and Poincare inequalities, which, for example, link variance to the expected size of the gradient norm.

= References
+ Primary reference: Chapters 0, 1 and 2 in #link("https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-2.pdf", 
"Vershynin").
+ Alternative: Up to Section 1.4 in #link("https://arxiv.org/pdf/2310.19244", "Rigollet and Hutter").
+ To appreciate measurability-related issues: Chapter 1 in #link("https://bookstore.ams.org/stml-75", "Kantor, Matousek, Samal").
+ Concentration of Measure from the perspective of convex geometry: #link("https://web.math.princeton.edu/~naor/homepage%20files/Concentration%20of%20Measure.pdf", "Naor").