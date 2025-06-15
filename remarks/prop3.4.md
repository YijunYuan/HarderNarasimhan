# Remarks on Proposition 3.4
## Remark 1
The sequence $\{x_i\}$ is constructed via recursively choosing the maximal element of the set
$$\mathscr{L}_k = \{y\in \mathscr{L}\backslash\{\bot\}\vert \mu_A(y)>\mu_A(x_k)\},\ k=0, 1,\cdots, \text{where } x_0=\top,$$
until it becomes empty (then just set $x_n=\top$).

**I believe we should impose an additional condition to the definition of $\mathscr{L}_k$:**
$$\mathscr{L}_k = \{y\in \mathscr{L}\backslash\{\bot\}\vert\ {\color{red}y < x_k},\ \mu_A(y)>\mu_A(x_k)\}.$$

1. This condition ensures that the sequence $\{x_i\}$ is strictly decreasing, which is what we need. Therefore, it is at least harmless. And Proposition 3.4 is successfully formalized with this modification.
2. I can't prove or disprove that it is covered by the conditions in the original context. This means that I do **NOT** know how to formalize Proposition 3.4 without this modification.

## Remark 2
Let me quote the original text:
> We can now show, by induction on the length of the above sequence,...

**I believe this does not accurately reflect the strategy of the proof.**

The proof just splits in to two cases: the length of the sequence $\{x_i\}$ (i.e. $n$) equals to $1$ or not. When dealing with the case $n>1$, we **never** use the argument like "if the result holds for all $n=1,2,\cdots,k-1$, then it holds for $n=k$". 

Althouth there does exist an induction in the proof
> ......Now if $y$ is an element of $\mathscr{L}\backslash \{\bot\}$ such that $\mu_A(y)\geq \mu_A(x_{n-1})$, then by the above statement, we can show by induction on $i$ that $y\leq x_i$ for any $i\in\{0,\cdots,n-1\}$......

This is not "`induction on the length`".