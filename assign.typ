#import "47834.typ": lecture
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *
#set-inherited-levels(0)
  
#show: lecture.with([Assignment 1], 0)
#show: show-theorion
#show link: underline

= Lower Bounds on Approximate Caratheodory (10 points)

We will show that the Approximate Caratheory's theorem can not be improved in high dimensions. For any dimension $d$, construct a set $X subset.eq RR^d$ contained in $BB_2 ={x:norm(x)_2<= 1}$ and a point $y$ in the convex hull of $X$ so that for all $k$ we have$
min_({x_1, dots x_k}in X) min_(alpha_i >= 0 \ sum_(i=1)^k alpha_i=1) norm(y-sum_(i=1)^n alpha_i x_i)_2 >= sqrt(1/k - 1/d).
$

= Pairwise Independence (10 points)
The purpose of this exercise is to demonstrate a specific sense in which pairwise independence is a much weaker condition than full independence. Concretely, given access to $n$ independent Rademacher variables, provide a deterministic recipe to construct at least $e^(c n)$ pairwise independent Rademacher variables for any $c>0$ of your choice.

= Random MaxCut (10 points)
Consider a random graph on $n$ vertices where each pair of vertices has a edge with probability $1 slash 2$, independently of other pairs. Every subset of vertices is associated with a cut, namely, edges with exactly one endpoint in a subset; the size of the cut is the number of such edges. Prove that with probability at least $0.999$, the maximum cut of such a graph is within $f(n) plus.minus g(n)$. Try to find the best such $f(n)$ and $g(n)$, but do not worry about the leading constant in $g(n)$.

= VC Dimension Examples (10 points)
Calculate the VC dimensions of:
#enum(spacing: 1em, indent: 1em)[
  The set of halfspaces (i.e., $bold(1)_(a^top x+b>= 0 : a in RR^n, b in RR)$) in $n$-dimensions][
  The set of $n$-dimensional spheres.
]
Lastly, prove for any $cal(H)_1$ and $cal(H)_2$ defined over the same feature space that $
"VC"(cal(H)_1 union cal(H)_2) <= "VC"(cal(H)_1) + "VC"cal(H)_2) + 1.
$
_Hint:_ Radon's theorem can be useful for the first part.

= Sparse Predictors (10 points)
Consider $cal(X)=RR^n$, and $cal(H)_k={bold(1)_(a^top x+b>= 0): a in RR^n, b in RR, norm(a)_0<= k}$ be the class of linear predictors that depend on at most $k$ coordinates. Prove that:
#enum(spacing: 1em, indent: 1em)[
  $"VC"(cal(H)_1)$ is at least $Omega(log n)$.][
  $"VC"(cal(H)_k)$ is at most $O (k log n/k)$.
]

= Learning by Asking is Faster (10 points)
The point of this exercise to show that if you are allowed to ask for the correct labels for points of your choice, you can learn with far less labeling/supervision. Concretely, construct a hypothesis class $cal(H) subset.eq {0,1}^([0,1])$ such that both conditions below are satisfied simultaneously:
#list(spacing: 1em, indent: 1em)[
  $cal(H)$ is (realizable) PAC learnable with sample complexity $Omega(log (1 slash delta) slash epsilon)$.][
  Consider a model where the learner can (A) _query_ the correct label for any given feature vector, and (B) additionally draw an infinite number of samples from the marginal distribution of $cal(D)$ on the feature space (without labels). It must be that, for any distribution $cal(D)$, as long as $"err"_cal(D)(h)=0$ for some $h in cal(H)$, a learning algorithm can make $O(log (1 slash epsilon))$ such _queries_ to produce a $h_cal(A) in cal(H)$ such that $"err"_cal(D)(h_cal(A))<= epsilon$. 
]
