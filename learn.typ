#import "47834.typ": lecture
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *
#set-inherited-levels(0)
  
#show: lecture.with([Statistical Learning Theory], 2)
#show: show-theorion
#show link: underline

Our goal in this lecture is to introduce Probably Approximate Correct (PAC) learning and build up to _the_ central result in learning theory, namely, that learnability for binary classification is exactly characterized by the VC dimension of the underlying hypothesis class. We will see a couple of applications of this result: the DKW inequality, and decision-theoretic learning of quantiles. At the end, we will also pave an alternative path to learning that relies on generalization through algorithmic stability.

But before we introduce the PAC framework, we pay our debt to concentration inequalities for nonlinear functions, which will be essential in deriving the results promised earlier.

#outline()

= Martingales
Concentration inequalities for nonlinear functions of independent variables boils down to concentration of linear forms of dependent, but controlled random variables. We will make this concrete in the next section. With this motivation, we introduce _martingales_ to capture sequences of such dependent random variables.

#definition[
  A sequence of random variables ${X_i}_(i>= 1)$ is a martingale if for all $n$, we have $
  EE[X_(n+1)| X_n,X_(n-1), dots, X_1] = X_n.
  $
  More generally, a sequence of random variables ${X_i}_(i>= 1)$ forms a martingale with respect to another sequence ${Y_i}_(i>= 1)$ if for all $n$, we have $
  EE[X_(n+1)| Y_n,Y_(n-1), dots, Y_1] = X_n,
  $
  where $X_n$ is measurable in (_read as_: completely determined given) $Y_1,dots Y_n$. The associated sequence ${X_(i+1)-X_i}_(i>=1)$ is called a _martingale difference sequence_.
]

As an example of martingale, consider prefix sums of independent zero-mean random variables, for example, $X_n = sum_(i<= n) Y_i$, where $Y_n tilde {plus.minus 1}$ are independent, which model random walks in one dimension. We can also have non-sum-like sequences, for example, $X_(n+1)=(1+Y_(n+1) sin(X_n))X_n$, where $Y_i$'s remain as defined previously.

Historically, the term _martingales_ originates from a certain class of French betting strategies; one can still find people puzzled about these on Youtube. The setup is as follows: at any stage one can bet any amount of choice on a fair random coin toss, receiving twice the initial amount upon success, and nothing on failure. Clearly, there is no way to predict a fair coin toss, and hence, one should not expect to make money in this circumstance. But consider the following strategy:
#align(center)[#quote[
  Starting with a $\$1$ bet in the first round, double the bet upon losing, and quit when you win.
]]
Since $2^(n+1) - 1 = 1+2+dots +2^n$, it is easy to observe that upon winning, one makes up all the money lost in the previous rounds and gains an extra dollar, ending up in the green. Winning in the long run happens almost surely, and hence, this specious argument seems to guarantee a small profit. Of course, one might run out of money this way, but consider having an infinite purse. Even then, we can observe that the return $S_n$ at end of round $n$ is distributed as $
S_n = cases(
  1 &"with probability" 1-1/2^n,
  -(2^n-1) &"with probability" 1/2^n
)
$
which on expectation is zero. In fact, $S_n$ forms a martingale sequence. (Verify this!) The almost surety of winning happens at the cost of cataclasmic losses with exponential small probability.

= Bounded Differences Inequality
We generalize the subgaussian character of sums of independent random variables to martingales.

#lemma[
  If $Delta_(j+1)|X_(1:j)=x_(1:j) tilde "SubGaussian"(sigma_j^2)$ for all $x_(1:j)$ and $j$, and ${Delta_n}$ forms a martingale difference sequence with respect to ${X_n}$, then $sum_(i=1)^n Delta_i tilde "SubGaussian"(sum_(i=1)^n sigma_i^2).$
]
#proof[
  The proof follows by repeated applications of $EE[EE[X|Y]]=EE[X]$, while noting that $Delta_(1:j)$ is measurable in $X_(1:j)$. $
  EE[e^t(sum_(i=1)^n (Delta_i - EE Delta_i))] &= EE_(X_(1:n-1))[EE_(X_n)[e^t(sum_(i=1)^n (Delta_i - EE Delta_i))|X_(1:n-1)]] \
  &= EE_(X_(1:n-1))[EE_(X_n)[e^t(Delta_n - EE Delta_n)|X_(1:n-1)]e^t(sum_(i=1)^(n-1) (Delta_i - EE Delta_i))]\
  &<= e^(-t^2 sigma_n^2 slash 2) EE[e^t(sum_(i=1)^(n-1) (Delta_i - EE Delta_i))] = dots = e^(t^2 sum_(i=1)^n sigma_i^2 slash 2)
  $
]

Our main result in this section is that any nonlinear function $f$ with independent random variables as arguments concentrates to its mean, as long as it can not changed a lot by tweaking a single argument in isolation. One unfortunate aspect of this result, although it will suffice for us in this lecture, is that the sensitivities to coordinates must be measured in a worst-case sense, that is, by fixing the other coordinates to their worst configuration. Time permitting, in later lectures, we will fix this and also extend the result to Lipschitz functions.
#theorem(title: "McDiarmid's Inequality")[
  Consider a $n$-variate function $f:cal(X)^n -> RR$. Define $
 delta_i (x_(1:n)) = max_(x in cal(X)) f(x_(1:i), x, x_(i+1:n)) - min_(y in cal(X)) f(x_(1:i), y, x_(i+1:n)).
$
Then, for any $t>0$ and $c_i >= norm(delta_i)_infinity := max_(x_(1:n)) delta_i (x_(1:n))$, we have that $
  Pr(abs(f(X_1, dots X_n) -EE f(X_1, dots X_n)) >= t) <= 2e^(-(2t^2)/(sum_(i=1)^n c_i^2)).
$
] <mcdiarmid>
#proof[
  We begin by noting that $f(X_(1:n)) - EE f(X_(1:n))$ can be decomposed as $
  f(X_(1:n)) - EE f(X_(1:n)) &= f(X_(1:n)) - EE_(X_n)[f(X_(1:n))|X_(1:n-1)] + EE_(X_n)[f(X_(1:n))|X_(1:n-1)] - EE[f(X_(1:n))] \
  &= sum_(i=1)^n EE[f(X_(1:n))|X_(1:i)] - EE[f(X_(1:n))|X_(1:i-1)].
$
Clearly, $Delta_i :=EE[f(X_(1:n))|X_(1:i)] - EE[f(X_(1:n))|X_(1:i-1)]$ forms a martingale difference sequence with respect to ${X_n}$, since $Delta_i$ is measurable in $X_(1:i)$ and $
  EE[Delta_(j+1)|X_(1:j)] = EE_(X_(j+1))[EE[f(X_(1:n))|X_(1:j+1)]] - EE[f(X_(1:n))|X_(1:j)] = 0.
$
It is plain to see that $Delta_i = EE_(Y_i,X_(i+1:n))[f(X_(1:n)) - f(X_(1:i-1), Y_i, X_(i+1:n))|X_(1:i)] <= c_i$, and hence it is subgaussian with variance proxy $c_i^2 slash 4$, by Hoeffding's lemma. Thus we have fulfilled all the requirements of the previous lemma, and hence $f(X_(1:n))$ is subgaussian with variance proxy $(sum_(i=1)^n c_i^2) slash 4$. The tail bound immediately follows from this observation.
]

== Application: Max Cut
As our first example, consider the $G(n, 1 slash 2)$ family of random graphs. This is a distribution over all undirected (simple) graphs over $n$ vertices where each pair of distinct vertices is connected by an edge with probability $1 slash 2$, independently of the other pairs. We are interested in figuring out the size of the maximum cut, that is, the the maximum number of edges that cross any partition of the vertex set, with probability $0.99$. Treating the presence of edges as independent Bernoulli variables, any balanced cut, one with nearly equal number of vertices on both sides, has $n^2/4 times 1/2 = n^2/8$ edges on expectation, and is subgaussian with variance proxy $n^2/4 times 1/2 times (1-1/2) = n^2/16$. Hence, since there are $2^n$ possible cuts in total, a blind application of the maximal inequality gives the size of the maximum cut to be $n^2/8 plus.minus O(sqrt(n^2/16 log 2^n)) = n^2/8 plus.minus O(n^(3 slash 2))$. 

While the maximal inequality gives the correct _expected_ size of the maxcut as $n^2/8 + C n^(3 slash 2)$, for some universal constant $C$, using McDiarmid, we will see that the fluctuations due to randomness are just $plus.minus O(n)$ in size. To see this, think of the maximum cut as a function of $binom(n, 2)$ indicator variables of individual edges, which go up (or down) by at most one while adding (or removing) an edge, that is $c_i=1$. As a consequence, we get the maximum cut lies in $n^2/8 + C n^(3 slash 2) plus.minus O(n)$.

== Application: Bin Packing
As a second example, consider $n$ items of independent random sizes ${X_i}$ in the range $[0,1]$. Let $Y_n$ be the minimum number of unit-sized bins required to pack these, where we cannot split an item between two bins. Imagine, for example, $X_i tilde "Unif"[0,1]$, in which case $EE[Y_n] >= ceil(sum_(i=1)^n X_i) = n slash 2$. Again, $Y_n$ can go up (or down) by at most one by increasing (or decreasing) the size of a single item. Hence, $Y_n$ lies in $EE[Y_n] plus.minus O(sqrt(n))$ with probability $0.99$. Thus, although $Y_n$ on any specific day involves a NP-hard problem, over provisioning boxes by a vanishingly small fraction fulfills the demand with high probability on any day without knowledge of the realized item sizes.

= PAC Learning
Let us first concretely define the learning task. We will imagine that there is a feature space $cal(X)$ and label space $cal(Y)$, and on top of this is a data-generating distribution $cal(D)$ supported on $cal(X) times cal(Y)$. A loss function $l:cal(Y)^2 -> RR$ assigns a loss to the prediction $hat(y) in cal(Y)$ when the correct label is $y$ as $l(hat(y), y)$. In this lecture, we will deal with binary classification, where $cal(Y)={0, 1}$ and $l(hat(y), y)= bold(1)_(hat(y) eq.not y)$, often termed the zero-one loss. Given this, we can define the population error of any classifier $h$ to be $
"err"_cal(D)(h) = EE_((x,y) tilde cal(D))[l(h(x), y)] = Pr_((x,y) tilde cal(D))(h(x) eq.not y).
$

Our first result is a negative one. Note that a random classifier has an error of $1 slash 2$. In words, the proposition states that no learning algorithm can have a significantly better error without observing a constant fraction of all the data points, even if a perfect classifier exists. If $cal(X)={0,1}^d$, this sample requirement for nontrivial error scales as $2^d$.

Note that if the latter requirement of a perfect classifier is dropped, then we can take $cal(D)$ to be the uniform distribution on $cal(X)$ augmented with $Pr(Y=1|X=x) tilde "Be"(1 slash 2)$ for all $x in cal(X)$, for which even the best classifier can do no better than half on error. But this is a setting in which knowing $cal(D)$ beforehand confers no advantage; hence, this does not capture a failure of learnability. 

#proposition(title: "No Free Lunch")[
  Consider any finite $cal(X)$, and any learning algorithm that upon observing $m$ samples produces a classifier $h_cal(A)$. Then, there exists a distribution $cal(D)$ supported on $cal(X)times {0,1}$ such that $EE["err"_cal(D)(h_cal(A))] >= 1/2(1-m/abs(cal(X)))$ while $min_(f^* in [0,1]^cal(X))"err"_cal(D)(f^*)=0$.
] <no-free-lunch>
#proof[
  Our proof essentially works via _Yao's minimax lemma_, although we will not call it by name. Instead of constructing a single distribution, we construct a distribution of distributions $cal(F)$ as follows. For any $bold(y) in {0,1}^cal(X)$, let $cal(D)_bold(y)$ be the distribution with uniform distribution on $cal(X)$, where each $x in cal(X)$ has a deterministic label $bold(y)(x)$. Clearly, $bold(y)$ itself is perfect classifier for $cal(D)_bold(y)$. Let $cal(F)$ be a uniform distribution over ${cal(D)_bold(y):bold(y) in {0,1}^cal(X)}$. Now, we observe for any algorithm $cal(A)$ that$
    max_(bold(y) in {0,1}^cal(X)) EE_(S^m tilde cal(D)_bold(y))["err"_cal(D)_bold(y) (h_cal(A))] &>= EE_(cal(D)_bold(y) tilde cal(F)) EE_(S^m tilde cal(D)_bold(y))["err"_cal(D)_bold(y) (h_cal(A))] \
    &= EE_(X^m tilde"Unif"(cal(X))) EE_(bold(y) tilde"Unif"({0,1}^cal(X)))[1/abs(cal(X)) sum_(x in cal(X)) bold(1)_(h_cal(A)(x) eq.not bold(y)(x)) ] \
    &>= EE_(X^m tilde"Unif"(cal(X))) EE_(bold(y) tilde"Unif"({0,1}^cal(X)))[1/abs(cal(X)) sum_(x in cal(X)-X^m) bold(1)_(h_cal(A)(x) eq.not bold(y)(x)) ] \
    &= EE_(S^m) [1/abs(cal(X)) sum_(x in cal(X)-X^m) EE_(y tilde"Unif"({0,1})) bold(1)_(h_cal(A)(x) eq.not bold(y)(x)) ] >= (abs(cal(X))-m)/(2abs(cal(X))),
  $
  where in the first equality, we use a _double sampling_ argument, namely that sampling $bold(y)$ uniformly randomly and then choosing $m$ samples from $cal(D)_bold(y)$ can also be seen as sampling $m$ feature vectors from the uniform distribution over $cal(X)$ and them choosing $bold(y)$ uniformly randomly. In the second equality, we use the fact that since components of $bold(y)$ are independent, even conditioned on $S^m$, $bold(y)(x)$ is a uniformly random binary label for all $x in.not X^m$, on which any predict rule makes error with probability $1 slash 2$. Finally, we note that due to sampling with replacement, $X^m$ captures at most $m$ distinct elements from $cal(X)$.
]

In the face of this impossibility, there can be two responses. The more obvious of these developments is to limit the class of distributions under consideration, so $cal(D)$ can no longer be arbitrary. One can hope that for _nice_ and _natural_ distributions such impossibilities do not arise. For a long as time, this was the only approach to learning, as embodied in classical (especially parametric) statistics. In this vein, one assumes that the true data-generating distribution $cal(D)^*$ belongs to some known class ${cal(D)_1, dots cal(D)_n}$, finite here for simplicity of illustration. As more samples are gathered from $cal(D)^*$, one can _identify_ the true distribution, at least in a functional sense. A severe disadvantage with this approach is that if $cal(D)^*$ happens to lie outside our considered class, it is unclear  how a learning algorithm of this sort performs, or if it converges, or if it does, does the convergent distribution yield a reasonable classifier for the true distribution.

The other recourse, and perhaps _the_ defining choice in learning theory, is to redefine the notion of success and seek a different sort of learning guarantee. Instead of limiting $cal(D)^*$, we choose a limited hypothesis class $cal(H)={h_1, dots h_n}$. Instead of succeeding in absolute terms, success of an (agnostic) learning algorithm lies in ensuring that the classifier it produces is almost as good as the best hypothesis in $cal(H)$. The advantage is immediate: by choosing $cal(H)$ to be the set of Bayes-optimal classifiers for ${cal(D)_1, dots cal(D)_n}$, one can ensure that the classifier produced is as good as the best classifier for the true data-generating distribution $cal(D)^*$, if $cal(D)^*$ lies in the aforementioned set, thus recovering the classical statistical guarantee. On the other hand, robustness to the latter assumption is built in, insofar that, even if all our models of $cal(D)^*$ were wrong, we still retain performance as good as the best hypothesis in $cal(H)$; thus this approach degrades the right way against mis-specification. This way of thinking in terms of a relative error guarantee is something even experts in other (classical) fields find hard to accept -- although the acceptance is growing by the day -- perhaps because hypothesis classes embody solution concepts and do not produce an explicit mechanistic description of how the data was generated. But to the extent one cares about minimizing the loss, this approach cannot be beat.

We begin with the definition of realizable PAC learning that makes the above setting concrete, but also does not quite deliver on what was promised. The _realizability_ assumption here is that there exists a perfect classifier in the hypothesis class $cal(H)$, or in other words, the learning guarantee only extends distributions $cal(D)$ for which this condition holds.

#definition[
  A hypothesis class $cal(H) subset.eq cal(Y)^cal(X)$ is realizable PAC learnable if there exists a sample complexity $m:(0,1)^2 -> NN$ and a learning algorithm $cal(A)$, which for any $epsilon,delta>0$ and distribution $cal(D)$ supported on $cal(X) times cal(Y)$, upon taking $m(epsilon, delta)$ samples produces a classifier $h_cal(A):cal(X) -> {0,1}$ such that with probability at least $1-delta$, we have $
  "err"_cal(D)(h_cal(A)) <= epsilon,
  $as long as there exists an $h^* in cal(H)$ such that $"err"_cal(D)(h^*)=0$.
]

The more general model, but one which is also computationally challenging, is agnostic PAC learning, which forgoes the realizability assumption, and gives a relative error guarantee, instead of an absolute one. The sample requirement here is also generally higher, as we will see.

#definition[
  A hypothesis class $cal(H) subset.eq cal(Y)^cal(X)$ is agnostic PAC learnable if there exists a sample complexity $m:(0,1)^2 -> NN$ and a learning algorithm $cal(A)$, which for any $epsilon,delta>0$ and distribution $cal(D)$ supported on $cal(X) times cal(Y)$, upon taking $m(epsilon, delta)$ samples produces a classifier $h_cal(A):cal(X) -> {0,1}$ such that with probability at least $1-delta$, we have $
  "err"_cal(D)(h_cal(A)) <= min_(h^* in cal(H)) "err"_cal(D)(h^*) + epsilon.
  $
]

= Finite Classes
As a warm-up, in this section, we consider the task of learning finite classes $cal(H)$. Along the way, we will develop the framework of learning infinite class (not all of are learnable!), which is our ultimate goal. For any $m$-sized sample set $S subset.eq cal(X) times cal(Y)$, let $"err"_S (h) = 1/m sum_(i=1)^m l(h(x_i), y_i)$ be the empirical error of the hypothesis $h$. We begin with realizable learning.

#theorem[
  Any finite hypothesis class $cal(H)$ is realizable PAC learnable with$
  m(epsilon, delta) = O((log (abs(cal(H)) slash delta))/epsilon) "samples."
  $
]
#proof[
  Certifying PAC learnability requires specifying a learning algorithm. We choose the most obvious one, namely, pick $h_cal(A) in cal(H)$ arbitrarily as long as $"err"_S (h_cal(A))=0$. Due to realizability, generically, such a choice always exists, else our claim is vacuous. What does failure to learn mean? Define $cal(H)_"Bad" = {h in cal(H): "err"_cal(D)(h)>epsilon}$. Now, failure is synonymous with $h_cal(A)$ in $cal(H)_"Bad"$, which only happens if there is a hypothesis $h$ in $cal(H)_"Bad"$ with $"err"_S (h)=0$. Now fix any $h in cal(H)_"Bad"$. We have $
  Pr("err"_S (h)=0) = product_(i=1)^m Pr(h(x_i)=y_i) = (1-epsilon)^m,\
  Pr("err"_cal(D) (h_A)) <= sum_(h in cal(H)_"Bad") Pr("err"_S (h)=0) = |cal(H)_"Bad"|(1-epsilon)^m <= abs(cal(H)) e^(-epsilon m),
  $
  where we use the inequality $1+x<=e^x$ for all $x$, concluding the claim.
]

For the agnostic case, we introduce the concept of uniform convergence, which requires that with enough samples, the maximum difference between the population error and the sample error across all hypothesis in the class can be made arbitrarily small. This means that the performance on the sample set transfers to the population. We will reuse this notion for infinite hypothesis classes.
#definition[
  A hypothesis class $cal(H) subset.eq cal(Y)^cal(X)$ exhibits uniform convergence with sample complexity $m_"UC" :(0,1)^2 -> NN$ if, for any $epsilon, delta>0$, upon taking $m_"UC" (epsilon, delta)$ samples from any distribution $cal(D)$, supported over $cal(X) times cal(Y)$, to form $S$, we have with probability at least $1-delta$ that $
  max_(h in cal(H)) |"err"_cal(D)(h) - "err"_S (h)| <= epsilon.
  $
]

We will now see that uniform convergence immediately implies agnostic PAC learnability.
#theorem[
  If a hypothesis class $cal(H)$ exhibits uniform convergence, then it is agnostic PAC learnable with sample complexity $m(epsilon,delta)=m_"UC" (epsilon/2, delta)$
] <agnostic-from-uc>
#proof[
  Again, we start with the learning algorithm, which picks $h_cal(A) in arg min_(h in cal(H)) "err"_(S)(h)$ arbitrarily. Let $h^* in arg min_(h in cal(H)) "err"_cal(D)(h)$. By uniform convergence, with probability $1-delta$, we have $
  "err"_cal(D) (h_cal(A)) <= "err"_cal(S) (h_cal(A)) + epsilon <= "err"_cal(S) (h^*) + epsilon <= "err"_cal(D) (h^*) + 2epsilon,
  $
  completing the proof.
]

While in general uniform convergence arguments require some care, for finite classes, uniform convergence follows essentially by a union bound.
#theorem[
  Any finite hypothesis class $cal(H)$ exhibits uniform convergence with $
  m_"UC" (epsilon,delta)=O((log abs(cal(H)) slash delta)/epsilon^2) "samples".
  $
]
#proof[
  Since $EE_S "err"_S (h) = "err"_cal(D) (h)$ for any fixed hypothesis $h$, we observe that $
  Pr(max_(h in cal(H)) |"err"_cal(D) (h) - "err"_S (h)| > epsilon) <= sum_(h in cal(H))Pr(|"err"_cal(D) (h) - "err"_S (h)| > epsilon) <= 2|cal(H)|e^(-2n epsilon^2),
  $
  where the last inequality follows from the tail bound for averages from the last lecture.
]

Combining the previous two results, we get the following corollary concerning the agnostic learning of finite hypothesis classes.

#corollary[
  Any finite hypothesis class $cal(H)$ is agnostic PAC learnable with$
  m(epsilon, delta) = O((log (abs(cal(H)) slash delta))/epsilon^2) "samples."
  $
]

= VC Dimension
Now, we are ready to extend learnability to infinite hypothesis classes. Not all hypothesis classes are learnable. Hence, a key question is to find out when learning is possible for infinite classes, by coming up with an appropriate notion of _size_ for hypothesis classes. 

#definition[
  For $C = {x_1, dots x_m} subset.eq cal(X)$ of finite size and hypothesis class $cal(H) subset.eq {0,1}^cal(X)$, let $
  cal(H)_C = {(h(x_1), dots h(x_m)) : h in cal(H)}
  $
  be the set of labelings $cal(H)$ induces on $C$. The VC dimension $"VC"(cal(H))$ of a hypothesis class $cal(H)$ is the size of the largest set with $abs(cal(H)_C) = 2^(abs(C))$, in other words, where all possible labelings are realized by $cal(H)$.
]

To state this explicitly, to establish that $"VC"(cal(H))=d$ for a class $cal(H)$, we must establish that there exists at least _one_ set $C$ of size $d$ where all possible labelings of $C$ are realized, thus, the VC dimension is at least $d$, and further that _all_ larger sets have at least one unrealizable labeling, implying the VC dimension is strictly less than $d+1$.

Let us look at a few examples. #enum(spacing: 1em, indent: 1em)[
  For $cal(X)=RR$, $cal(H)={bold(1)_(x<=a): a in RR}$ has VC dimension one. Clearly, on $C={0}$, this class realizes a positive label by choose $a=1$ and a negative label by choosing $a=-1$. Furthermore, for any two point set $C={a,b}$ where $a<=b$ generically, a negative label on $a$ and a positive label on $b$ are not realizable simultaneously. Similarly, $"VC"({bold(1)_(x>=a): a in RR})=1$.][
  Take $cal(X)=RR$. The VC dimension of $cal(H)={bold(1)_(a<=x<=b): a,b in RR}$ is two. It is easy to see that there exists a two-point set, e.g., ${0, 1}$, where all possible labelings are realized. For any three-point set ${a,b,c}$ with $a<=b<=c$, a negative label in the middle and positive labels at extremities is unrealizable.][
  Take $cal(X)=RR^2$. The VC dimension of all (closed) axis-aligned rectangles is four. Note that not all four point sets, e.g., ${(0,0), (0,1), (1,0), (1,1)}$, can be assigned arbitrary labelings, but that's okay, because we just need to show _one_ four-point set that can be labeled in all possible ways. Such a set exists, e.g., ${(1,0), (0,1), (-1,0), (0,-1)}$. Arguing that every five-point set has an unrealizable labeling is trickier. The cleanest argument here is that the smallest axis-aligned rectangle containing any five-point set is also the smallest axis-aligned rectangle for some four-point subset of the original set. Hence, the point in the "middle" can not be assigned a label independently of the other four.
]

= Learning VC Classes
At this point, it might not be obvious why VC dimension is the correct notion of _size_ for learning. The theorem on sufficiency will shed some light on this, but far more obvious is the fact that finite VC dimension is necessary for learning.

#corollary(number: 4.1)[
  For any hypothesis class $cal(H)$ with infinite VC dimension, and learning algorithm $cal(A)$ that produces the classifier $h_cal(A)$ after seeing $m$ samples, for any $epsilon>0$, there exists a distribution $cal(D)$ such that $EE["err"_cal(D) (h_cal(A))] >=  1/2 - epsilon$ and $min_(h in cal(H)) "err"_cal(D)(h)=0$. Thus, a finite VC dimension is necessary for realizable (and hence also agnostic) PAC learning.
]
#proof[
  Since the VC dimension of $cal(H)$ is unbounded, we can find arbitrarily large subsets $C$ of $cal(X)$ on which $cal(H)$ can realize all possible labelings. We apply @no-free-lunch to such a set of size $m slash epsilon$.
]

In fact, from a quick examination of the proof of @no-free-lunch, we can also see that the sample complexity of realizable and agnostic learning must scale as $Omega("VC"(cal(H)))$, although the argument does not by itself imply a correct, that is, tight, bound on other parameters.

Now, we will prove that a finite VC dimension is sufficient for learning. We will focus on the agnostic case, which also implies realizable learnability. In fact, we will prove a near-optimal sample complexity bound for agnostic PAC learning. This proof is interesting to the extent that it will involve all little probabilistic tools that we have developed so far, ranging from symmetrization to maximal inequalities and McDiarmid's inequality. 

#theorem[
  Any hypothesis class $cal(H)$ with a finite VC dimension $d$ exhibits uniform convergence with sample complexity $
  m_"UC" (epsilon, delta) = O((d + log 1 slash delta)/epsilon^2).
  $
] <unif-from-vc>
#proof[
  In fact, we will prove a bound of $O((d log d slash epsilon + log 1 slash delta) slash epsilon^2)$ on the sample complexity, which is worse by logarithmic factors, because proving the tight bound, although very much in reach of the present course, is slightly painful.
  
  Fix any hypothesis class $cal(H)$ with VC dimension $d$, and a random sample set $S$ of size $m$ drawn from $cal(D)$. Notice that $S |-> max_(h in cal(H)) abs("err"_cal(D)(h) - "err"_S (h))$ goes up (or down) by at most one on changing a sample. Hence, by @mcdiarmid, we get that $
   Pr(abs( max_(h in cal(H)) abs("err"_cal(D)(h) - "err"_S (h)) - EE_S [max_(h in cal(H)) abs("err"_cal(D)(h) - "err"_S (h))] >= t )) <= 2e^(-2m t^2).
  $
  To make the right side at most $delta$, $m$ needs to be at least $log (2 slash delta) slash epsilon^2$. This explains the second term in the sample complexity. 
  
  #lemma[For a sample set of size $m$ and a class of VC dimension $d$, we have that
    $
    EE_S [max_(h in cal(H)) abs("err"_cal(D)(h) - "err"_S (h))] <= O(sqrt((d log 2m)/m)).
    $
  ] <massart-lemma>
  To conclude the claim and note the necessity of the first term in the sample complexity, we use the maximal inequality above that specifically deals with VC classes.
]

#proof(title: [Proof of @massart-lemma])[
  On the face of it, @massart-lemma looks exactly like the standard maximal inequality. After all, $"err"_S (h) - "err"_cal(D)(h)$ for any fixed $h$ is exactly zero-mean and, being an average over $m$ independent samples, subgaussian with variance proxy $1 slash m$. The catch is that the standard maximal inequality scales here as $sqrt(log |cal(H)|)$, which is just a fancy way of recovering our finite hypothesis results. With some manipulation, we will show the _effective_ size of $cal(H)$, one that matters here anyway, is $O(m^d)$, using the lemma below.

  #lemma(title: "Sauer-Shelah-Perles Lemma")[
    For any hypothesis class $cal(H)$ with VC dimension $d$ and a set $C$ of size $m$ on the same feature space, we have that $
    abs(cal(H)_C) <= sum_(k=0)^d binom(m, k).
    $
    In particular, if $m$ is at least $d$, then $abs(cal(H)_C) <= O(m^d)$.
  ] <sauer-lemma>
  The main trick is to use symmetrization. Observe the following sequence of inequalities. $
  &EE_S [max_(h in cal(H)) abs("err"_cal(D)(h) - "err"_S (h))] \
  &=_(1) EE_S [max_(h in cal(H)) abs(EE_(S') "err"_S'(h) - "err"_S (h))] \
  &<=_2 EE_(S,S') [max_(h in cal(H)) abs("err"_S'(h) - "err"_S (h))]\
  &= EE_(S,S') [max_(h in cal(H)) abs(1/m sum_(i=1)^m (l(h(x'_i), y'_i) - l(h(x_i), y_i)))]\
  &=_3 EE_(S,S')[EE_(sigma tilde {plus.minus 1}^m)[max_(h in cal(H)) abs(1/m sum_(i=1)^m sigma_i (l(h(x'_i), y'_i) - l(h(x_i), y_i))) mid(|) S,S']]\
  &=_4 EE_(S,S')[EE_(sigma tilde {plus.minus 1}^m)[max_(h in cal(H)_(S union S')) abs(1/m sum_(i=1)^m sigma_i (l(h(x'_i), y'_i) - l(h(x_i), y_i))) mid(|) S,S']]\
  &<=_5 C sqrt((log max_(S subset.eq cal(X), abs(S)<=2m)abs(cal(H)_(S)))/m)\
  &<=_6 O(sqrt((d log m)/m))
  $
  Here (1) introduces $S'$ as $m$ samples, chosen independently from $S$, and (2) follows from Jensen's inequality, while noting that $x |-> abs(x)$ is a convex function, and taking a maximum over a family of functions preserves convexity. Step (3) follows from noting that for any $S,S'$ exchanging the corresponding samples between these at any index $i$ results in a new pair of sets that are equiprobable. The key step is (4), where we narrow $cal(H)$ to $cal(H)_(S union S')$, since the quantity being maximized only depends on the samples via the signs realized by $cal(H)$ on the same set. Step (5) follows by the standard maximal inequality, having fixed $S,S'$. In step (6), we apply @sauer-lemma.

  Thus, we have the desired claim. But it is worth taking a moment to appreciate why all the machinations above were needed. Clearly, replacing the population error by the sample error on newly sampled points was instrumental in ultimately narrowing $cal(H)$ to $cal(H)_(S union S')$, by saying that only the signs realized on some $2m$ points matter. But, one might also be tempted to directly use the maximal inequality at the end of step (2), without introducing Rademacher random variables. This idea fails. While even at the end of step (2) we could have narrowed $cal(H)$ to $cal(H)_(S union S')$, now the index set being maximized over is stochastic, while an implicit promise in the maximal inequality is that the index set is deterministic, or at lease independent of other sources on randomness. Had we conditioned on $S,S'$ at this stage, that would have fixed the stochastic index set, but made the remaining quantity deterministic too, losing the subgaussian character.
]

Before proving @sauer-lemma, let us take a second to review its implication. It says for any class with bounded VC dimension, the number of labelings grows polynomially in the size of the set. If on the other hand, the VC dimension is infinite, then, by definition, there are sets of any needed size where the number of labelings are exponentially many. The lemma rules out all possibilities in the middle, that is, those associated with a superpolynomial but subexponential growth for all sets simultaneously. This is also why VC dimension sharply characterizes learnability. Each class is either learnable, to a nontrivial degree, with a constant number of samples, or unlearnable altogether. There is no in-between.

#proof(title: [Proof of @sauer-lemma])[
  The proof proceeds by induction on $m+d$. The base cases can be verified separately. Fix a hypothesis class $cal(H)$ with VC dimension $d$ and a set $C ={x_1,dots x_m} subset.eq cal(X)$. Let $C'=C-{x_1}$ and $cal(H)'={h in cal(H): exists h' in cal(H), h'(x_1)=1-h(x_1)}$. Now, we claim that $
  abs(cal(H)_C) = abs(cal(H)_C') + abs(cal(H)'_C').
  $
  In words, all labelings of $C'$ have either a unique extension to $C$ under $cal(H)$, in which case they are counted in the first term, or admit two extensions, with both $plus.minus$ signs on $x_1$, to $C$, in which case they are accounted for once in the first term and again in the second term. 
  
  Let us construct another hypothesis class $cal(H)''$ which is the same as $cal(H)'$ except that $x_1$ is not in its domain. (If this makes you uneasy, it is also fine to assign all of $cal(H)''$ an arbitrary label on $x_1$.) Since $C'$ does not contain $x_1$, $cal(H)'_C'$ and $cal(H)''_C'$ are identical. Further, we claim that the VC dimension of $cal(H)''$ is at most $d-1$, because if all labelings of a set $D$ are attained by $cal(H)''$, then $cal(H)$ attains all labelings on $C union {x_1}$. We then apply the inductive hypothesis on $cal(H)_C'$ and $cal(H)''_C'$ to get $
  |cal(H)_C| <= sum_(k=0)^d binom(m-1, k) + sum_(k=0)^(d-1) binom(m-1, k) =  binom(m-1, 0) + sum_(k=1)^d (binom(m-1, k) + binom(m-1, k-1)) =  sum_(k=0)^d binom(m, k),
  $
  where we use the identity that $binom(m,k) = binom(m, k-1) + binom(m-1, k-1)$. The following display completes the final clause, as long as $m>=d$. $
  abs(cal(H)_C) <= (m/d)^d sum_(k=0)^d binom(m, k) (d/m)^k <= (m/d)^d (1+ d/m)^m <= ((m e)/d)^d
  $
]

Using @agnostic-from-uc, uniform convergence of finite VC classes implies agnostic PAC learnability.
#corollary[
  Any hypothesis class $cal(H)$ with a finite VC dimension $d$ is agnostic PAC learnable with sample complexity $
  m(epsilon, delta) = O((d + log 1 slash delta)/epsilon^2).
  $
]

Finally, we remark the sample complexity derived above can be improved to scale as $1 slash epsilon$ in the realizable case. The proof of this result utilizes a nice double sampling argument.

== Application: DKW Inequality
Consider the task of estimating the CDF $F$ of a continuous real-valued random variable given $m$ independent samples. A natural choice of the estimator is $
hat(F)(t) = 1/m sum_(i=1)^m bold(1)_(x_i <= t)
$
Using subgaussian tail bounds, for any fixed $t$, $Pr(|F(t) - hat(F)(t)| >= t) <= 2e^(-2m t^2)$. The Dvoeretzky-Keifer-Wolfowitz inequality says the same bound holds uniformly, without needing a union bound.

#theorem(title: "DKW Inequality")[
  $Pr(sup_(t in RR) |F(t) - hat(F)(t)| >= t) <= 2e^(-2m t^2)$
]
The proof is a simple application of @unif-from-vc -- this is after all a statement about uniform convergence -- if one were willing to ignore the precise constants, since the VC dimension of the indicator variables of ${(-infinity, a]: a in RR}$ is one. In terms of history, the DKW inequality predates VC theory by a good couple of decades.

== Application: Learning Quantiles
Consider an inventory replenishment problem for nondurable goods, typically termed the newsvendor problem. At the end of each day, a store owner owners orders $a$ goods to delivered the next morning. The stochastic demand $X in [0,1]$ is realized the next day. The resultant loss is $
l(X,a) = rho [X-a]_+ + (1-rho) [a-X]_+,
$
which imposes unequal penalties for over and under meeting the demand. Here $[X-a]^+ = max{X-a, 0}$. We are interested in pick an action that minimizes the expected cost $EE_X [l(X,a)]$. Since $a |-> l(X,a)$ is convex, the subgradient is $
d/(d a) EE_X [l(X,a)] = EE_X [ rho bold(1)_(X>a) - (1-rho) bold(1)_(X<=a)] = rho Pr(X>a) - (1-rho) Pr(X<=a),
$
and hence the optimal choice $a$ is the bottom $rho$-quantile of $cal(D)$.

What can we do if $cal(D)$ is unknown and instead we observe $m$ samples from $cal(D)$? By the DKW inequality, we can choose $hat(a)$ to be the bottom $rho$-quantile of observed samples, and guarantee that $F(hat(a)) = rho plus.minus O(1 slash sqrt(m))$ with probability $0.99$. An exercise in integration by parts gives (Verify!) $
EE_X [l(X,a)] = rho integral_a^1 Pr(X>=x) d x + (1-rho) integral_(-1)^a Pr(X<=x) d x. 
$
Now, we can see how good $hat(a)$ is by observing $
EE_X [l(X, hat(a))] - EE_X [l(X, a^*)] = integral_(hat(a))^a^* (rho-F(x)) d x <= O(1/sqrt(m)).
$

= Algorithmic Stability
The plan here was to carve an alternative path to generalization and learning via (uniform) stability of the learning algorithm. Instead of focusing on the characteristics of the hypothesis class, this is an algorithm-centric approach. Being short on time, we will instead consider a simple example that deals with Leave-One-Out (LOO) stability and proves generalization in expectation.

#definition[
  The Leave-One-Out (LOO) stability $Delta(cal(A),S^(m+1))$ of a learning algorithm $cal(A)$ with respect to a sample $S={(x_i, y_i)}_(i in [m+1])$ of size $m+1$ is defined as $
  Delta(cal(A), S) = 1/(m+1) sum_(i=1)^(m+1) (l(h_cal(A_i)(x_i), y_i) - l(h_(cal(A))(x_i), y_i)),
  $
  where the algorithm $cal(A)$ receives $S^(m+1)$ as its input and $cal(A)_i$ receives all samples but $(x_i, y_i)$.
]

The following is a funny sort of in-expectation generalization guarantee that compares the population error of an algorithm that is given $m$ samples to the in-sample error on $m+1$ samples, instead of $m$ as one would expect. Nevertheless, this will suffice for our application. In fact, for reasonable learning algorithms, for example, if one chooses a hypothesis with the smallest error on training data, this upper bounds the usual generalization error in expectation, up to a small $1 slash m$ additive term (Verify this!).
#theorem[ 
For any distribution $cal(D)$, we have that $
EE_(S^m)["err"_cal(D)(h_cal(A)')] = EE_(S^(m+1))["err"_(S^(m+1))(h_cal(A))] + EE_(S^(m+1))[Delta(cal(A), S^(m+1))],
$where $cal(A)'$ and $cal(A)$ receive $S^m$ and $S^(m+1)$ as their inputs, respectively.
]
#proof[
  The proof is a simple consequence of the definition. $
  EE_(S^(m+1))[Delta(cal(A), S^(m+1))] &= 1/(m+1) sum_(i=1)^(m+1) EE_(S^(m+1))[l(h_cal(A_i)(x_i), y_i)] - EE_(S^(m+1))[1/(m+1) sum_(i=1)^(m+1) l(h_cal(A)(x_i), y_i)]\
  &= 1/(m+1) sum_(i=1)^(m+1) EE_(S^(m))EE_((x,y) tilde cal(D))[l(h_cal(A)'(x), y)] - EE_(S^(m+1))["err"_(S^(m+1))(h_cal(A))]\
  &= EE_(S^(m))["err"_cal(D)(h_(cal(A)'))] - EE_(S^(m+1))["err"_(S^(m+1))(h_cal(A))]
  $
]

As an application, consider the task of learning $d$-dimensional axis-aligned rectangles in the realizable case. Our learning algorithm in this case simply outputs the smallest axis-aligned rectangle containing all positive examples. The empirical error given any number of samples is zero. We will soon see that the worst-case LOO stability over any $m+1$ example is at most $(2d)/(m+1)$. Hence, this algorithm given $m$ samples has a population error of at most $(2d)/(m+1)$, matching the sample complexity of $O(d slash epsilon)$ we would get from the VC approach. To see this bound on the LOO stability, note that the smallest rectangle is supported by at least one sample on every one of its $2d$ facets, and a facet shifts only if all samples supporting it are deleted, and thus, $cal(A)_i$ and $cal(A)$ are identical on all except at most $4$ indices.

= References
+ Primary reference: Chapters 2--6 and 28 in #link("https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf", 
"Shalev-Shwartz and Ben-David").
+ Alternative: Chapters 2 and 3 in #link("https://www.dropbox.com/s/38p0j6ds5q9c8oe/10290.pdf?dl=1", "Mohri, Rostamizadeh, Talwalkar").
+ Alternative: Chapter 5 in #link("https://www.cs.cornell.edu/jeh/book.pdf", "Blum, Hopcroft, Kannan").
+ Bounded Differences Inequality: Chapters 5 and 6 in #link("http://wwwusers.di.uniroma1.it/~ale/Papers/master.pdf", "Dubhashi and Panconesi").